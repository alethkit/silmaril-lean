module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (Meaning Outcome)
open Lists.Iteration (truth)

/-- Interpret a prepared closure by the core body denotation. Restore the
caller bindings on both exits and retain the state left by the callee. -/
def denoteDispatch (program : Program) (available : List DeclarationId)
    (callee : Lists.Value) (actual : Actual) : Meaning Lists.Value :=
  fun caller =>
    match prepareExpanded program available actual callee caller with
    | .error error next => .error error next
    | .ok (.builtin id args) next => Builtins.invoke id args next
    | .ok (.closure plan) next =>
      match denoteBody program (withoutDeclaration available plan.id) plan.body next with
      | .ok flow final => .ok (callValue flow) (restoreCaller caller final)
      | .error error final => .error error (restoreCaller caller final)

/-- Apply an evaluated callee and operands, with expansion before dispatch. -/
def denoteApplication (program : Program) (available : List DeclarationId)
    (shape : ArgumentShape) : List Lists.Value → Meaning Lists.Value
  | [] => throw .notCallable
  | callee :: operands => do
    let actual ← (shape.collect operands).expand
    denoteDispatch program available callee actual

/-- Direct state-and-error denotation of a resolved expression. Expressions
recurse on syntax and delegate closure bodies to the finite core denotation. -/
def denoteExpr (program : Program) (available : List DeclarationId) : Expr → Meaning Lists.Value
  | .atom code => Lists.denote code
  | .call callee positional keywords star starStar => do
    let callable ← denoteExpr program available callee
    let values ← (argumentExprs positional keywords star starStar).attach.mapM fun operand => do
      have := argumentSize callee positional keywords star starStar operand.property
      denoteExpr program available operand.val
    denoteApplication program available (argumentShape positional keywords star starStar) (callable :: values)
  | .branch test yes no => do
    let flag ← truth (← denoteExpr program available test)
    if flag then denoteExpr program available yes else denoteExpr program available no
  | .logical op left right => do
    let value ← denoteExpr program available left
    let flag ← truth value
    if (if op = .and then flag else !flag) then denoteExpr program available right else pure value
termination_by expression => sizeOf expression
decreasing_by all_goals first | assumption | (simp_wf; omega)

end Silmaril.Languages.Starlark.Functions.Lowering
