module

public import Silmaril.Languages.PythonStarlark.ClosedReturn.Defs
import all Silmaril.Languages.Starlark.Resolve.Defs

public section

namespace Silmaril.Proofs.Languages.PythonStarlark.ClosedReturn

open Silmaril.Languages.PythonStarlark.ClosedReturn Silmaril.Languages

private theorem resolve_expr {Literal : Type} (literal : Literal → Starlark.SourceExpr)
    (resolved : Literal → Starlark.ResolvedExpr)
    (resolve : String → Except Starlark.StaticError Starlark.Ref)
    (leaf : ∀ value, Starlark.resolveExpr resolve (literal value) = .ok (resolved value))
    (expr : Expr Literal) :
    Starlark.resolveExpr resolve (expr.starlark literal) = .ok (expr.starlark resolved) := by
  induction expr with
  | literal value => exact leaf value
  | binary op left right leftIH rightIH =>
    simp [Expr.starlark, Starlark.resolveExpr, leftIH, rightIH, bind, Except.bind, pure, Except.pure]

theorem int_resolves (body : IntBody) :
    Starlark.resolveFunctionBody [] [] body.starlark = .ok (.ret (some (body.value.starlark .int))) := by
  simp [IntBody.starlark, Starlark.resolveFunctionBody, Starlark.resolveStmt,
    resolve_expr .int .int _ (fun _ => rfl), bind, Except.bind, pure, Except.pure]

theorem numeric_resolves (body : NumericBody) :
    Starlark.resolveFunctionBody [] [] body.starlark =
      .ok (.ret (some (body.body.value.starlark NumericLiteral.starlarkResolved))) := by
  have leaf (value : NumericLiteral) :
      Starlark.resolveExpr (Starlark.resolveName [] []) (NumericLiteral.starlark value) =
        .ok (NumericLiteral.starlarkResolved value) := by
    cases value with
    | int => rfl
    | bool b => cases b <;> rfl
  simp [NumericBody.starlark, Starlark.resolveFunctionBody, Starlark.collectLocals, Starlark.resolveStmt,
    resolve_expr _ _ _ leaf, bind, Except.bind, pure, Except.pure]

end Silmaril.Proofs.Languages.PythonStarlark.ClosedReturn
