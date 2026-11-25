module

public import Silmaril.Languages.Starlark.Lists.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

/-- Resolved expressions with nested calls and collection operands.
An atom uses the existing call-free collection expression language. -/
inductive Expr where
  | atom (expression : Lists.Expr)
  | list (elements : List Expr)
  | tuple (elements : List Expr)
  | index (receiver subscript : Expr)
  | call (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
      (star starStar : Option Expr)
  | branch (test yes no : Expr)
  | logical (op : LogicalOp) (left right : Expr)

@[expose] def Expr.callPos (callee : Expr) (positional : List Expr) : Expr :=
  .call callee positional [] none none

end Silmaril.Languages.Starlark.Functions.Lowering
