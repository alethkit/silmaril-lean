module

import Silmaril.Languages.Starlark.Functions.Thms
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

private def execute (body : Body) :=
  let initial := ([events, destination].foldl Lists.State.allocateSlot {}).write
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

end Silmaril.Languages.Starlark.Functions
