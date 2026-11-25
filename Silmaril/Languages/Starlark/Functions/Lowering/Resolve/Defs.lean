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

private abbrev Tracked := StateT (List Binding) (Except Error)

private def resolveRead (context : Context) (name : String) : Tracked Expr := do
  if name.toList.head? = some '$' then
    throw (.reservedName name)
  match Starlark.resolveName context.locals context.globals name with
  | .ok (.bound binding) =>
    modify (binding :: ·)
    return .atom (.read (.bound binding))
  | .ok (.predeclared value) => return .atom (.read (.predeclared value))
  | .error error =>
    match Lists.Builtin.resolve name with
    | some builtin => return .atom (.builtin builtin)
    | none => throw (.lexical error)

private def resolveScalar (context : Context) : Starlark.SourceExpr → Tracked Expr
  | .int value => pure (.atom (.scalar (.int value)))
  | .read name => resolveRead context name
  | .unary op _ => throw (.unsupportedUnary op)
  | .binary op .. => throw (.unsupportedBinary op)
  | .logical op left right =>
    return .logical op (← resolveScalar context left) (← resolveScalar context right)
  | .conditional test yes no =>
    return .branch (← resolveScalar context test) (← resolveScalar context yes)
      (← resolveScalar context no)

private def resolveExpr (context : Context) : SourceExpr → Tracked Expr
  | .scalar expression => resolveScalar context expression
  | .string text => pure (.atom (.string text))
  | .call callee positional keywords star starStar => do
    let callee ← resolveExpr context callee
    let positional ← positional.attach.mapM fun ⟨expression, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      resolveExpr context expression
    let keywords ← keywords.attach.mapM fun ⟨(name, expression), member⟩ => do
      have := List.sizeOf_lt_of_mem member
      return (name, ← resolveExpr context expression)
    let star ← star.mapM (resolveExpr context)
    let starStar ← starStar.mapM (resolveExpr context)
    return .call callee positional keywords star starStar
  | .conditional test yes no =>
    return .branch (← resolveExpr context test) (← resolveExpr context yes) (← resolveExpr context no)
  | .logical op left right =>
    return .logical op (← resolveExpr context left) (← resolveExpr context right)
termination_by expression => sizeOf expression
decreasing_by all_goals (simp_all <;> omega)

/-- Resolve all operands and both branches, reporting lexical reads for closure
capture. Predeclared constants and built-ins have no slot to capture. -/
def resolveTracked (context : Context) (expression : SourceExpr) : Except Error (Expr × List Binding) :=
  (resolveExpr context expression []).map fun (resolved, reads) => (resolved, reads.reverse)

/-- Resolve a normalized expression in an already collected lexical context.
The checked executor validates the explicit keyword names in the result. -/
def resolve (context : Context) (expression : SourceExpr) : Except Error Expr :=
  (resolveTracked context expression).map Prod.fst

end Silmaril.Languages.Starlark.Functions.Lowering.Resolve
