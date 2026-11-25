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
  | dict (entries : List (Expr × Expr))
  | index (receiver subscript : Expr)
  /-- Normalize each omitted bound to an atom containing `None`. -/
  | slice (receiver start stop stride : Expr)
  | call (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
      (star starStar : Option Expr)
  | branch (test yes no : Expr)
  | logical (op : LogicalOp) (left right : Expr)

@[expose] def Expr.callPos (callee : Expr) (positional : List Expr) : Expr :=
  .call callee positional [] none none

theorem sliceOperandSize {receiver start stop stride operand : Expr}
    (member : operand ∈ [receiver, start, stop, stride]) :
    sizeOf operand < sizeOf (Expr.slice receiver start stop stride) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp <;> omega

end Silmaril.Languages.Starlark.Functions.Lowering
