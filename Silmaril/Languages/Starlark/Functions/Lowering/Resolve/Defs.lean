module

public import Silmaril.Languages.Starlark.Functions.Lowering.Defs
public import Silmaril.Languages.Starlark.Resolve.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering.Resolve

/-- Normalized, unresolved input for the expression lowerer. The scalar
constructor accepts existing scalar trees, subject to the checks below. -/
inductive SourceExpr where
  | scalar (expression : Starlark.SourceExpr)
  | string (text : String)
  | call (callee : SourceExpr) (positional : List SourceExpr)
      (keywords : List (String × SourceExpr)) (star starStar : Option SourceExpr)
  | conditional (test yes no : SourceExpr)
  | logical (op : LogicalOp) (left right : SourceExpr)

/-- Names from the caller's already collected lexical scope. A nearer
captured binding can be supplied under the name and scope it has in this frame. -/
structure Context where
  locals : List String := []
  globals : List String := []

inductive Error where
  | lexical (error : StaticError)
  | reservedName (name : String)
  | unsupportedUnary (op : UnaryOp)
  | unsupportedBinary (op : BinaryOp)
  deriving DecidableEq, Repr

private def resolveRead (context : Context) (name : String) : Except Error Expr := do
  if name.toList.head? = some '$' then
    throw (.reservedName name)
  match Starlark.resolveName context.locals context.globals name with
  | .ok ref => return .atom (.read ref)
  | .error error =>
    match Lists.Builtin.resolve name with
    | some builtin => return .atom (.builtin builtin)
    | none => throw (.lexical error)

private def resolveScalar (context : Context) : Starlark.SourceExpr → Except Error Expr
  | .int value => .ok (.atom (.scalar (.int value)))
  | .read name => resolveRead context name
  | .unary op _ => .error (.unsupportedUnary op)
  | .binary op .. => .error (.unsupportedBinary op)
  | .logical op left right =>
    return .logical op (← resolveScalar context left) (← resolveScalar context right)
  | .conditional test yes no =>
    return .branch (← resolveScalar context test) (← resolveScalar context yes)
      (← resolveScalar context no)

/-- Resolve all operands and both branches before running the lowerer.
Call syntax keeps the four normalized operand classes separate. Repeated
explicit names are checked from the emitted call by the checked executor. -/
def resolve (context : Context) : SourceExpr → Except Error Expr
  | .scalar expression => resolveScalar context expression
  | .string text => .ok (.atom (.string text))
  | .call callee positional keywords star starStar => do
    let callee ← resolve context callee
    let positional ← positional.attach.mapM fun ⟨expression, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      resolve context expression
    let keywords ← keywords.attach.mapM fun ⟨(name, expression), member⟩ => do
      have := List.sizeOf_lt_of_mem member
      return (name, ← resolve context expression)
    let star ← star.mapM (resolve context)
    let starStar ← starStar.mapM (resolve context)
    return .call callee positional keywords star starStar
  | .conditional test yes no =>
    return .branch (← resolve context test) (← resolve context yes) (← resolve context no)
  | .logical op left right =>
    return .logical op (← resolve context left) (← resolve context right)
termination_by expression => sizeOf expression
decreasing_by all_goals (simp_all <;> omega)

end Silmaril.Languages.Starlark.Functions.Lowering.Resolve
