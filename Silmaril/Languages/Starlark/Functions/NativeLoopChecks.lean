module

import Silmaril.Languages.Starlark.Functions.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions

private def slot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Lists.Expr := .read (.bound (slot name))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def list (values : List Int) : Lists.Expr := .list (operandList (values.map int))
private def set (name : String) (value : Lists.Expr) : Body := .total (.atomic (.assign (slot name) value))
private def append (name : String) (value : Lists.Expr) : Body :=
  .total (.atomic (.eval (.append (read name) value)))

private def program : Program := #[⟨{ positional := [⟨slot "xs", none⟩] }, [], [],
  .seq (append "xs" (int 3)) (.returnExpr (.atom (read "xs")))⟩]

private def iterable : Lowering.Expr :=
  .callPos (.atom (read "prepare")) [.atom (read "xs")]

private def execute (loop : Body) :=
  let setup := [Body.define (slot "prepare") 0, set "xs" (list [1, 2]), set "alias" (read "xs"),
    set "seen" (list []), set "x" (int 7)]
  let initial : Lists.State := { heap := #[⟨.list [], false⟩], iterators := [0] }
  runChecked program (setup.foldr Body.seq loop) initial

private def hasList (state : Lists.State) (name : String) (expected : List Int) : Bool :=
  match state.bindingValue (slot name) with
  | .ok (.list address) =>
    match Lists.listElements address state with
    | .ok values _ => decide (values = expected.map fun n => .scalar (.int n))
    | _ => false
  | _ => false

private def visit : Body := append "seen" (read "x")

-- The operand mutates its own returned list once. The snapshot includes the new item.
#guard
  match execute (.forInExpr (slot "x") iterable visit) with
  | .ok (.ok .next final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3] && hasList final "seen" [1, 2, 3]
  | _ => false

-- The inner call mutates the list, then the enclosing len fails before there is a loop target write.
#guard
  let failure := Lowering.Expr.callPos (.atom (.builtin .len))
    [.logical .and iterable (.atom (int 9))]
  match execute (.forInExpr (slot "x") failure visit) with
  | .ok (.error (.builtinType .len (.scalar (.int 9))) final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3] && hasList final "seen" [] &&
      match final.bindingValue (slot "x") with
      | .ok (.scalar (.int 7)) => true
      | _ => false
  | _ => false

-- Successful acquisition blocks alias writes. Body failure releases only the loop's own guard.
#guard
  match execute (.forInExpr (slot "x") iterable (append "alias" (int 4))) with
  | .ok (.error (.activeIteration address) final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3] &&
      match final.bindingValue (slot "xs"), Lists.appendAt address (.scalar (.int 4)) final with
      | .ok (.list original), .ok _ amended => original == address && hasList amended "xs" [1, 2, 3, 4]
      | _, _ => false
  | _ => false

#guard
  match execute (.forInExpr (slot "x") iterable (.returnExpr (.atom (read "x")))) with
  | .ok (.ok (.returned (.scalar (.int 1))) final) =>
    final.iterators == [0] && hasList final "xs" [1, 2, 3]
  | _ => false

#guard
  let invalid := Lowering.Expr.call (.atom (.builtin .len)) []
    [("x", .atom (int 1)), ("x", .atom (int 2))] none none
  let skipped := Lowering.Expr.logical .or (.atom (int 1)) invalid
  match execute (.forInExpr (slot "x") skipped .breakLoop), execute (.forInExpr (slot "x") iterable .breakLoop) with
  | .error (.duplicateExplicitKeyword "x"), .ok (.ok .next _) => true
  | _, _ => false

end Silmaril.Languages.Starlark.Functions
