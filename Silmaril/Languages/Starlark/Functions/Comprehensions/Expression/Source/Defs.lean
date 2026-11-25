module

public import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

open Lowering (Admitted Scratch)

/-- The existing expression-lowering profile applies to each operand,
including operands on statically admitted but dynamically skipped paths. -/
inductive Expression.Admitted : Expression → Prop where
  | plain {value : Lowering.Expr} : Lowering.Admitted value → Expression.Admitted (.plain value)
  | list {comp : ListComp} : Lowering.Admitted comp.iterable →
      (∀ expr ∈ comp.rest.operands, Lowering.Admitted expr) →
      (∀ name ∈ comp.locals, ¬ Scratch 0 name) → Expression.Admitted (.list comp)
  | dict {comp : DictComp} : Lowering.Admitted comp.iterable →
      (∀ expr ∈ comp.operands, Lowering.Admitted expr) →
      (∀ name ∈ comp.locals, ¬ Scratch 0 name) → Expression.Admitted (.dict comp)
  | callPos {callee : Lowering.Expr} {arguments : List Expression} :
      Lowering.Admitted callee → (∀ arg ∈ arguments, arg.Admitted) →
      Expression.Admitted (.callPos callee arguments)
  | branch {test yes no : Expression} :
      test.Admitted → yes.Admitted → no.Admitted → Expression.Admitted (.branch test yes no)
  | logical {op : LogicalOp} {left right : Expression} :
      left.Admitted → right.Admitted → Expression.Admitted (.logical op left right)

end Silmaril.Languages.Starlark.Functions.Comprehensions
