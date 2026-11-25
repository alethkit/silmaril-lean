module

import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Lists.Freeze.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Functions

open Lists (Address State)
open Lists.Iteration (Flow)
open scoped Lowering.Quote

private def localName (name : String) : Binding := ⟨.local, name⟩
private def global (name : String) : Binding := ⟨.global, name⟩
private def target := global "target"
private def alias := global "alias"
private def events := global "events"
private def marker := localName "marker"
private def result := localName "result"

private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def integer (n : Int) : Lowering.Expr := .atom (int n)
private def string (value : String) : Lowering.Expr := .atom (.string value)
private def append (binding : Binding) (value : Lists.Expr) : Body :=
  .total (.atomic (.eval (.append (read binding) value)))
private def assign (binding : Binding) (value : Lowering.Expr) : Body := .assignExpr binding value

private def program : Program := #[
  ⟨{ positional := [⟨marker, none⟩, ⟨result, none⟩] }, [], [⟨events, events⟩],
    .seq (append events (read marker)) (.returnExpr (.atom (read result)))⟩,
  ⟨{}, [], [⟨events, events⟩, ⟨target, target⟩],
    .seq (append events (int 3)) (.seq (append target (int 77)) (.returnExpr (integer (-1))))⟩]

private def note (n : Int) (value : Lowering.Expr) : Lowering.Expr :=
  .callPos (.atom (read (global "note"))) [integer n, value]

private def originalList : Lowering.Expr := .list [integer 7]
private def originalDict : Lowering.Expr := .dict [(string "b", integer 7), (string "a", integer 8)]

private def execute (container : Lowering.Expr) (code : Body) (prepare : State → State := id) :
    Except CallStaticError (Lists.Outcome Flow) := do
  let root : State := ([events, target].foldl State.allocateSlot { iterators := [99] }).write marker (.scalar (.int 42))
  let setup := [assign events (.list []), assign target container, assign alias (.atom (read target)),
    .define (global "note") 0, .define (global "grow") 1].foldr Body.seq (.total (.atomic .pass))
  match ← runChecked program setup root with
  | .ok .next state => runChecked program code (prepare state)
  | out => return out

private def address (state : State) : Option Address := do
  let value ← (state.bindingValue target).toOption
  let aliasValue ← (state.bindingValue alias).toOption
  if aliasValue = value then value.address? else none

private def cell (state : State) : Option Lists.Cell := do
  let address ← address state
  state.heap[address]?

private def observed (state : State) (effects : List Int) : Bool :=
  state.iterators == [99] && (state.slots marker).isNone &&
    decide (state.bindings marker = some (.scalar (.int 42))) &&
    match state.bindingValue events with
    | .ok (.list address) =>
      decide (state.heap[address]? = some ⟨.list (effects.map fun n => .scalar (.int n)), false⟩)
    | _ => false

private def setIndex (index : Lowering.Expr) : Body :=
  .setIndexExpr (note 2 (.atom (read alias))) index (note 1 (integer 9))

private def followedByEffect (code : Body) : Body := .seq code (.evalExpr (note 99 (integer 0)))

private def frozen (state : State) : State := state.freeze (state.bindingValue target).toOption.toList

private def listCell (values : List Int) (frozen : Bool := false) : Option Lists.Cell :=
  some ⟨.list (values.map fun n => .scalar (.int n)), frozen⟩

private def dictCell (entries : List (String × Int)) (frozen : Bool := false) : Option Lists.Cell :=
  some ⟨.dict (entries.map fun (key, value) => ⟨.string key, [.string key], .scalar (.int value)⟩), frozen⟩

-- The final index uses the list length after `grow` appends through the shared address.
#guard
  match execute originalList (setIndex (.callPos (.atom (read (global "grow"))) [])) with
  | .ok (.ok .next state) => observed state [1, 2, 3] && decide (cell state = listCell [7, 9])
  | _ => false

#guard
  let writes := Body.seq (setIndex (note 3 (string "b"))) (setIndex (note 3 (string "c")))
  match execute originalDict writes with
  | .ok (.ok .next state) =>
    observed state [1, 2, 3, 1, 2, 3] && decide (cell state = dictCell [("b", 9), ("a", 8), ("c", 9)])
  | _ => false

-- A failure at any operand keeps its effects, skips later work, and leaves the original cell intact.
#guard
  let failAt := fun n => Lowering.Expr.callPos (.atom (.builtin .len)) [note n (integer 9)]
  let receiver := note 2 (.atom (read alias))
  let subscript := note 3 (integer 0)
  let rhs := note 1 (integer 9)
  let failed := fun code trace => match execute originalList (followedByEffect code) with
    | .ok (.error (.builtinType .len (.scalar (.int 9))) state) =>
      observed state trace && decide (cell state = listCell [7])
    | _ => false
  failed (.setIndexExpr receiver subscript (failAt 1)) [1] &&
    failed (.setIndexExpr (failAt 2) subscript rhs) [1, 2] &&
    failed (.setIndexExpr receiver (failAt 3) rhs) [1, 2, 3]

#guard
  let invalidTarget := Body.setIndexExpr (note 2 (integer 7)) (note 3 (integer 0)) (note 1 (integer 9))
  let invalidKey := setIndex (note 3 (.list []))
  match execute originalList (followedByEffect invalidTarget), execute originalDict (followedByEffect invalidKey) with
  | .ok (.error .assignmentTarget first), .ok (.error (.unhashableKey (.list _)) second) =>
    observed first [1, 2, 3] && observed second [1, 2, 3] &&
      decide (cell first = listCell [7] ∧ cell second = dictCell [("b", 7), ("a", 8)])
  | _, _ => false

-- List bounds win over freezing. Dictionary freezing wins over an unhashable key.
#guard
  match execute originalList (followedByEffect (setIndex (note 3 (integer 2)))) frozen,
      execute originalList (followedByEffect (setIndex (note 3 (integer 0)))) frozen,
      execute originalDict (followedByEffect (setIndex (note 3 (.list [])))) frozen with
  | .ok (.error (.indexRange 2 1) first), .ok (.error (.frozen list) second),
    .ok (.error (.frozen dict) third) =>
    observed first [1, 2, 3] && observed second [1, 2, 3] && observed third [1, 2, 3] &&
      decide (address second = some list ∧ address third = some dict ∧ cell first = listCell [7] true ∧
        cell second = listCell [7] true ∧ cell third = dictCell [("b", 7), ("a", 8)] true)
  | _, _, _ => false

-- The alias is guarded during iteration. Failure releases the loop's guard and keeps the caller's stack.
#guard
  let iterate := fun subscript => Body.forInExpr (localName "item") (.atom (read target))
    (followedByEffect (setIndex (note 3 subscript)))
  match execute originalList (iterate (integer 0)), execute originalDict (iterate (.list [])) with
  | .ok (.error (.activeIteration list) first), .ok (.error (.activeIteration dict) second) =>
    observed first [1, 2, 3] && observed second [1, 2, 3] &&
      decide (address first = some list ∧ address second = some dict ∧ cell first = listCell [7] ∧
        cell second = dictCell [("b", 7), ("a", 8)])
  | _, _ => false

-- Subscript assignment introduces no namespace binding. Function and module writes reach the same global list.
#guard
  let commands : List Modules.Resolve.Command := [
    .assign "xs" starlark%[[1, 2]],
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "put" {} (.setIndex starlark%[pick(xs)] starlark%[pick(-1)] starlark%[pick(22)]),
    .eval starlark%[put()], .setIndex starlark%[pick(xs)] starlark%[pick(0)] starlark%[pick(33)]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "xs" with
    | some (.list address) => decide (state.heap[address]? = listCell [33, 22] true)
    | _ => false
  | _ => false

end Silmaril.Languages.Starlark.Functions
