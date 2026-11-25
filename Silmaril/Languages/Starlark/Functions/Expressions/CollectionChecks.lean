module

import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Functions.Lowering

open scoped Quote

private def marker : Binding := ⟨.local, "marker"⟩
private def argument : Binding := ⟨.local, "value"⟩
private def events : Binding := ⟨.global, "events"⟩
private def noteName : Binding := ⟨.global, "note"⟩
private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def integer (value : Int) : Expr := .atom (.scalar (.int value))
private def string (value : String) : Expr := .atom (.string value)

private def program : Program := #[
  ⟨{ positional := [⟨marker, none⟩, ⟨argument, none⟩] }, [], [⟨events, events⟩],
    .seq (.total (.atomic (.eval (.append (read events) (read marker)))))
      (.returnExpr (.atom (read argument)))⟩]

private def note (n : Int) (value : Expr) : Expr :=
  .callPos (.atom (read noteName)) [integer n, value]

private def length (value : Expr) : Expr := .callPos (.atom (.builtin .len)) [value]

private def root : Lists.State := (({} : Lists.State).allocateSlot events).write marker (.scalar (.int 99))

private def setup : Body := .seq (.total (.atomic (.assign events (.list .empty)))) (.define noteName 0)

private def execute (expression : Expr) : Lists.Outcome Lists.Value :=
  Lists.Outcome.resume (run program setup root) fun _ => denoteExpr program [0] expression

private def integers (values : List Int) : List Lists.Value := values.map fun n => .scalar (.int n)

private def observed (state : Lists.State) (trace : List Int) : Bool :=
  decide (state.bindings marker = some (.scalar (.int 99)) ∧ state.slots marker = none) &&
    match state.bindingValue events with
    | .ok (.list address) => decide (state.heap[address]? = some ⟨.list (integers trace), false⟩)
    | _ => false

-- Each call runs once, and allocation keeps the values in element order.
#guard
  let expression := Expr.index (.list [note 1 (integer 17), note 2 (integer 22)]) (note 3 (integer (-1)))
  match execute expression with
  | .ok (.scalar (.int 22)) state =>
    observed state [1, 2, 3] && state.heap.any (fun cell => decide (cell.contents = .list (integers [17, 22])))
  | _ => false

-- The index operand mutates the receiver through an alias before the read.
#guard
  match execute (.index (note 1 (.atom (read events))) (note 2 (integer (-1)))) with
  | .ok (.scalar (.int 2)) state => observed state [1, 2]
  | _ => false

-- Failure stops later operands and leaves the display itself unallocated.
#guard
  let expression := Expr.list [note 1 (integer 17), length (note 2 (integer 9)), note 3 (integer 22)]
  match execute expression with
  | .error (.builtinType .len (.scalar (.int 9))) state =>
    observed state [1, 2] && (state.heap.toList.filter (fun cell => match cell.contents with
      | .list _ => true
      | _ => false)).length == 1
  | _ => false

#guard
  let failedReceiver := Expr.index (length (note 1 (integer 9))) (note 2 (integer 0))
  let failedOperand := Expr.index (.list [note 1 (integer 17)]) (length (note 2 (integer 9)))
  let badTarget := Expr.index (note 1 (integer 17)) (note 2 (integer 0))
  match execute failedReceiver, execute failedOperand, execute badTarget with
  | .error (.builtinType .len (.scalar (.int 9))) first,
    .error (.builtinType .len (.scalar (.int 9))) second, .error .indexTarget third =>
    observed first [1] && observed second [1, 2] && observed third [1, 2] &&
      second.heap.any (fun cell => decide (cell.contents = .list (integers [17])))
  | _, _, _ => false

-- The normalized source uses the same declaration and module evaluator as other expressions.
#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "driver" {} (.ret (some starlark%[[pick(17), pick(22),][pick(-1)]])),
    .assign "out" starlark%[driver()]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 22)))
  | _ => false

#guard
  let bad := Expr.call (.atom (.builtin .len)) [] [("x", integer 0), ("x", integer 1)] none none
  let expression := Expr.branch (integer 1) (integer 2) (.list [.index (.list []) bad])
  match runChecked program (.returnExpr expression) {} with
  | .error (.duplicateExplicitKeyword "x") => true
  | _ => false

#guard
  match execute (.tuple [note 1 (integer 17), note 2 (integer 22)]) with
  | .ok (.tuple address) state =>
    let key : Lists.Key := [.openTuple, .scalar (.int 17), .scalar (.int 22), .closeTuple]
    observed state [1, 2] && decide (state.heap[address]? = some ⟨.tuple (integers [17, 22]) (some key), false⟩)
  | _ => false

#guard
  match execute (.tuple [note 1 (integer 17), length (note 2 (integer 9)), note 3 (integer 22)]) with
  | .error (.builtinType .len (.scalar (.int 9))) state =>
    observed state [1, 2] && state.heap.all (fun cell => match cell.contents with
      | .tuple .. => false
      | _ => true)
  | _ => false

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .assign "out" starlark%[(pick(17), pick(22),)[pick(-1)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 22)))
  | _ => false

private def dictionary (state : Lists.State) (entries : List (String × Int)) : Bool :=
  let expected := entries.map fun (name, value) =>
    (⟨.string name, [.string name], .scalar (.int value)⟩ : Lists.Entry)
  decide (state.heap[3]? = some ⟨.dict expected, false⟩)

private def pairs : List (Expr × Expr) := [
  (note 1 (string "b"), note 2 (integer 17)), (note 3 (string "a"), note 4 (integer 22))]

-- Allocation precedes the first operand. Each pair is inserted in source order.
#guard
  match execute (.dict pairs) with
  | .ok (.dict 3) state => observed state [1, 2, 3, 4] && dictionary state [("b", 17), ("a", 22)]
  | _ => false

#guard
  let later := (note 7 (string "later"), note 8 (integer 9))
  let duplicate := (note 5 (string "b"), note 6 (integer 33))
  match execute (.dict (pairs ++ [duplicate, later])) with
  | .error (.duplicateKey (.string "b")) state =>
    observed state [1, 2, 3, 4, 5, 6] && dictionary state [("b", 17), ("a", 22)]
  | _ => false

#guard
  let bad := (note 5 (.list []), note 6 (integer 9))
  let later := (note 7 (string "later"), note 8 (integer 9))
  match execute (.dict (pairs ++ [bad, later])) with
  | .error (.unhashableKey (.list address)) state =>
    observed state [1, 2, 3, 4, 5, 6] && dictionary state [("b", 17), ("a", 22)] &&
      address > 3 && decide (state.heap[address]? = some ⟨.list [], false⟩)
  | _ => false

-- An operand error takes precedence over entry validation and keeps the allocated dictionary.
#guard
  let keyError := Expr.dict [(length (note 1 (integer 9)), note 2 (integer 17))]
  let valueError := Expr.dict [(note 1 (.list []), length (note 2 (integer 9)))]
  match execute keyError, execute valueError with
  | .error (.builtinType .len (.scalar (.int 9))) first, .error (.builtinType .len (.scalar (.int 9))) second =>
    observed first [1] && observed second [1, 2] && dictionary first [] && dictionary second []
  | _, _ => false

#guard
  let duplicate := (note 5 (string "b"), note 6 (integer 33))
  let expression := Expr.dict (pairs ++ [duplicate, (note 7 (string "later"), note 8 (integer 9))])
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .error (.duplicateKey (.string "b")) direct, .error (.duplicateKey (.string "b")) lowered =>
    decide (lowered.heap = direct.heap) && observed lowered [1, 2, 3, 4, 5, 6] &&
      match lowered.bindingValue target with
      | .error (.uninitialized binding) => binding == target
      | _ => false
  | _, _ => false

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .assign "out" starlark%[{ (pick(7),) : pick(22), }[(pick(7),)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 22)))
  | _ => false

private def omitted : Expr := .atom (.scalar .none)

private def onlyEventsList (state : Lists.State) : Bool :=
  state.heap.toList.countP (fun cell => match cell.contents with
    | .list _ => true
    | _ => false) == 1

-- The slice reads after the bound effects, including those on its own receiver.
#guard
  let expression := Expr.slice (note 1 (.atom (read events))) (note 2 omitted)
    (note 3 omitted) (note 4 (integer (-2)))
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .ok (.list address) direct, .ok .next lowered =>
    observed direct [1, 2, 3, 4] && observed lowered [1, 2, 3, 4] &&
      decide ((direct.bindingValue events).toOption ≠ some (.list address) ∧
        direct.heap[address]? = some ⟨.list (integers [4, 2]), false⟩ ∧
        lowered.heap = direct.heap ∧ (lowered.bindingValue target).toOption = some (.list address))
  | _, _ => false

#guard
  let slice := fun start stop stride => (Lists.sliceElements (integers [0, 1, 2, 3, 4]) start stop stride).toOption
  let noneValue : Lists.Value := .scalar .none
  let intValue := fun i => Lists.Value.scalar (.int i)
  decide (slice (intValue (-4)) (intValue (-1)) (intValue 2) = some (integers [1, 3]) ∧
    slice (intValue 100) (intValue (-100)) (intValue (-2)) = some (integers [4, 2, 0]) ∧
    slice noneValue (intValue (-1)) (intValue (-1)) = some [] ∧
    slice (intValue (-100)) noneValue (intValue (-1)) = some [] ∧
    slice (intValue (-100000000000)) (intValue 100000000000) (intValue 100000000000) = some (integers [0]) ∧
    (Lists.sliceElements [] noneValue noneValue (intValue (-1))).toOption = some [])

-- Empty slices still allocate mutable list cells, even when read from a frozen source.
#guard
  let source : Lists.Cell := ⟨.list (integers [7]), true⟩
  let state : Lists.State := { heap := #[source] }
  match Lists.readSlice (.list 0) (.scalar .none) (.scalar (.int 0)) (.scalar .none) state with
  | .ok (.list address) next =>
    decide (address = 1 ∧ next.heap = #[source, ⟨.list [], false⟩])
  | _ => false

-- A failure in a bound skips later operands and the allocation. The lowered destination stays unbound.
#guard
  let expression := Expr.slice (note 1 (.atom (read events))) (length (note 2 (integer 9)))
    (note 3 omitted) (note 4 (integer 1))
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .error (.builtinType .len (.scalar (.int 9))) direct, .error (.builtinType .len (.scalar (.int 9))) lowered =>
    observed direct [1, 2] && observed lowered [1, 2] &&
      onlyEventsList direct && decide (lowered.heap = direct.heap) &&
      match lowered.bindingValue target with
      | .error (.uninitialized binding) => binding == target
      | _ => false
  | _, _ => false

-- A later operand failure takes precedence over receiver or bound validation.
#guard
  let bad := Expr.atom (.scalar (.bool true))
  match execute (.slice (note 1 (integer 42)) (note 2 bad) (length (note 3 (integer 9)))
      (note 4 (integer 0))) with
  | .error (.builtinType .len (.scalar (.int 9))) state => observed state [1, 2, 3] && onlyEventsList state
  | _ => false

-- Validation waits for the operands. Receiver, stride, start and stop are then checked in order.
#guard
  let readEvents := Expr.atom (read events)
  let bad := Expr.atom (.scalar (.bool true))
  let failed := fun receiver start stop stride expected =>
    match execute (.slice (note 1 receiver) (note 2 start) (note 3 stop) (note 4 stride)) with
    | .error error state => error == expected && observed state [1, 2, 3, 4] && onlyEventsList state
    | _ => false
  failed (integer 42) bad bad (integer 0) .sliceTarget &&
    failed readEvents bad bad bad (.sliceStrideType (.scalar (.bool true))) &&
    failed readEvents bad bad (integer 0) .zeroSliceStride &&
    failed readEvents bad bad omitted (.sliceStartType (.scalar (.bool true))) &&
    failed readEvents omitted bad omitted (.sliceStopType (.scalar (.bool true)))

-- A normalized function returns a fresh outer list whose nested values still alias the original.
#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .assign "inner" starlark%[[7]], .assign "items" starlark%[[inner, [8]]],
    .define "driver" {} (.ret (some starlark%[pick(items)[pick(None) :: pick(-1)]])),
    .assign "out" starlark%[driver()],
    .setIndex starlark%[inner] starlark%[0] starlark%[42],
    .setIndex starlark%[out] starlark%[0] starlark%[None],
    .assign "shared" starlark%[out[1][0]], .assign "untouched" starlark%[items[1][0]],
    .assign "tupleKey" starlark%[{(0, 1, 2)[pick(1):] : 9}[(1, 2)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "inner", published.exports.lookup "items", published.exports.lookup "out" with
    | some (.list inner), some (.list items), some (.list out) =>
      decide (items ≠ out ∧ state.heap[out]? = some ⟨.list [.scalar .none, .list inner], true⟩ ∧
        published.exports.lookup "shared" = some (.scalar (.int 42)) ∧
        published.exports.lookup "untouched" = some (.scalar (.int 8)) ∧
        published.exports.lookup "tupleKey" = some (.scalar (.int 9)))
    | _, _, _ => false
  | _ => false

end Silmaril.Languages.Starlark.Functions.Lowering
