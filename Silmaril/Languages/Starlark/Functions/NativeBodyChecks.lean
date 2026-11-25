module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions

private def events : Binding := ⟨.global, "events"⟩
private def mark : Binding := ⟨.global, "mark"⟩
private def destination : Binding := ⟨.local, "out"⟩

private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def int (value : Int) : Lists.Expr := .scalar (.int value)

private def program : Program :=
  let parameter : Binding := ⟨.local, "n"⟩
  #[⟨{ positional := [⟨parameter, none⟩] }, [], [⟨events, events⟩],
    .seq (.total (.atomic (.eval (.append (read events) (read parameter)))))
      (.returnExpr (.atom (read parameter)))⟩]

private def visit (value : Int) : Lowering.Expr :=
  .callPos (.atom (read mark)) [.atom (int value)]

private def failure : Lowering.Expr := .callPos (.atom (.builtin .len)) [visit 1]

private def execute (body : Body) (locals : List Binding := []) :=
  let initial := (([events, destination] ++ locals).foldl Lists.State.allocateSlot {}).write
    destination (.scalar (.int 7))
  let setup := Body.seq (.total (.atomic (.assign events (.list .empty)))) (.define mark 0)
  runChecked program (.seq setup body) initial

private def observed (state : Lists.State) (expectedEvents : List Int) (expectedOut : Int) : Bool :=
  match state.bindingValue events, state.bindingValue destination with
  | .ok (.list address), .ok (.scalar (.int out)) =>
    match Lists.listElements address state with
    | .ok values _ => out == expectedOut && decide (values = expectedEvents.map fun n => .scalar (.int n))
    | _ => false
  | _, _ => false

-- The nested RHS call extends the shared list before len fails.
#guard
  match execute (.assignExpr destination failure) with
  | .ok (.error (.builtinType .len (.scalar (.int 1))) final) => observed final [1] 7
  | _ => false

private def select (number : Int) : Body :=
  .seq (.assignExpr destination (visit number)) (.returnExpr (.atom (read destination)))

private def branch (test : Lowering.Expr) : Body := .branchExpr test (select 2) (select 3)

private def checkedBranch (condition chosen : Int) : Bool :=
  match execute (branch (visit condition)) with
  | .ok (.ok (.returned (.scalar (.int result))) final) =>
    result == chosen && observed final [condition, chosen] chosen
  | _ => false

-- The condition mutates once, then only its selected branch can write or return.
#guard checkedBranch 1 2 && checkedBranch 0 3

#guard
  match execute (branch failure) with
  | .ok (.error (.builtinType .len (.scalar (.int 1))) final) => observed final [1] 7
  | _ => false

#guard
  let invalid := Lowering.Expr.call (.atom (.builtin .len)) []
    [("x", .atom (int 1)), ("x", .atom (int 2))] none none
  let skipped := Lowering.Expr.logical .or (.atom (int 1)) invalid
  match execute (.assignExpr destination skipped), execute (branch skipped) with
  | .error (.duplicateExplicitKeyword "x"), .error (.duplicateExplicitKeyword "x") => true
  | _, _ => false

#guard
  match execute (.branchExpr (.atom (int 1)) (.total (.atomic .pass)) .breakLoop) with
  | .error .breakOutsideLoop => true
  | _ => false

-- The final RHS read still sees the old destination. Both writes to it occur
-- after evaluating the RHS, and the later write wins.
#guard
  let other : Binding := ⟨.local, "other"⟩
  let target : Lists.Iteration.LoopTarget := .sequence [.name destination, .unpack [destination, other]]
  let rhs : Lowering.Expr := .tuple [visit 1, .list [visit 2, .atom (read destination)]]
  match execute (.assignTargetExpr target rhs) [other],
      execute (Lowering.lowerAssignTarget target rhs).code [other] with
  | .ok (.ok .next direct), .ok (.ok .next lowered) =>
    observed direct [1, 2] 2 && observed lowered [1, 2] 2 &&
      decide ((direct.bindingValue other).toOption = some (.scalar (.int 7)) ∧ direct.heap = lowered.heap)
  | _, _ => false

-- A failed RHS reaches no target. A failed nested node keeps the earlier
-- sibling's write. The staged code retains the same heap and error in both cases.
#guard
  let other : Binding := ⟨.local, "other"⟩
  let target : Lists.Iteration.LoopTarget := .sequence [.name destination, .unpack [destination, other]]
  let check := fun rhs expected trace output =>
    match execute (.assignTargetExpr target rhs) [other],
        execute (Lowering.lowerAssignTarget target rhs).code [other] with
    | .ok (.error error direct), .ok (.error loweredError lowered) =>
      error == expected && loweredError == expected &&
        observed direct trace output && observed lowered trace output &&
        (direct.bindingValue other).toOption.isNone && decide (direct.heap = lowered.heap)
    | _, _ => false
  check failure (.builtinType .len (.scalar (.int 1))) [1] 7 &&
    check (.tuple [visit 1, .list [visit 2]]) (.unpackArity 2 1) [1, 2] 1

end Silmaril.Languages.Starlark.Functions
