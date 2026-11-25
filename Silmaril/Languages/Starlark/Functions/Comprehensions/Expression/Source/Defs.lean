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
  | listClauses {locals : List Binding} {target : Lists.Iteration.LoopTarget}
      {iterable : Expression} {rest : Tail Lowering.Expr Expression} :
      iterable.Admitted → (∀ operand ∈ rest.clauseOperands, operand.Admitted) →
      Lowering.Admitted rest.headValue → (∀ name ∈ locals, ¬ Scratch 0 name) →
      Expression.Admitted (.listClauses locals target iterable rest)
  | dictClauses {locals : List Binding} {target : Lists.Iteration.LoopTarget}
      {iterable : Expression} {rest : Tail (Lowering.Expr × Lowering.Expr) Expression} :
      iterable.Admitted → (∀ operand ∈ rest.clauseOperands, operand.Admitted) →
      Lowering.Admitted rest.headValue.1 → Lowering.Admitted rest.headValue.2 →
      (∀ name ∈ locals, ¬ Scratch 0 name) →
      Expression.Admitted (.dictClauses locals target iterable rest)
  | listComprehension {locals : List Binding} {target : Lists.Iteration.LoopTarget}
      {iterable : Expression} {rest : Tail Expression Expression} :
      iterable.Admitted → (∀ operand ∈ rest.clauseOperands, operand.Admitted) →
      rest.headValue.Admitted → (∀ name ∈ locals, ¬ Scratch 0 name) →
      Expression.Admitted (.listComprehension locals target iterable rest)
  | dictComprehension {locals : List Binding} {target : Lists.Iteration.LoopTarget}
      {iterable : Expression} {rest : Tail (Expression × Expression) Expression} :
      iterable.Admitted → (∀ operand ∈ rest.clauseOperands, operand.Admitted) →
      rest.headValue.1.Admitted → rest.headValue.2.Admitted →
      (∀ name ∈ locals, ¬ Scratch 0 name) →
      Expression.Admitted (.dictComprehension locals target iterable rest)
  | listDisplay {elements : List Expression} :
      (∀ element ∈ elements, element.Admitted) → Expression.Admitted (.listDisplay elements)
  | tupleDisplay {elements : List Expression} :
      (∀ element ∈ elements, element.Admitted) → Expression.Admitted (.tupleDisplay elements)
  | dictDisplay {entries : List (Expression × Expression)} :
      (∀ entry ∈ entries, entry.1.Admitted) → (∀ entry ∈ entries, entry.2.Admitted) →
      Expression.Admitted (.dictDisplay entries)
  | index {receiver subscript : Expression} :
      receiver.Admitted → subscript.Admitted → Expression.Admitted (.index receiver subscript)
  | slice {receiver start stop stride : Expression} :
      (∀ operand ∈ [receiver, start, stop, stride], operand.Admitted) →
      Expression.Admitted (.slice receiver start stop stride)
  | callPos {callee : Lowering.Expr} {arguments : List Expression} :
      Lowering.Admitted callee → (∀ arg ∈ arguments, arg.Admitted) →
      Expression.Admitted (.callPos callee arguments)
  | call {callee : Expression} {positional : List Expression} {keywords : List (String × Expression)}
      {star starStar : Option Expression} :
      callee.Admitted → (∀ arg ∈ Lowering.argumentExprs positional keywords star starStar, arg.Admitted) →
      Expression.Admitted (.call callee positional keywords star starStar)
  | branch {test yes no : Expression} :
      test.Admitted → yes.Admitted → no.Admitted → Expression.Admitted (.branch test yes no)
  | logical {op : LogicalOp} {left right : Expression} :
      left.Admitted → right.Admitted → Expression.Admitted (.logical op left right)

/-- The checked lowering assumptions for store operands apply at every leaf. -/
inductive AssignmentPattern.Admitted : AssignmentPattern → Prop where
  | name (binding : Binding) : AssignmentPattern.Admitted (.name binding)
  | subscript {receiver index : Lowering.Expr} :
      Lowering.Admitted receiver → Lowering.Admitted index → AssignmentPattern.Admitted (.subscript receiver index)
  | sequence {children : List AssignmentPattern} :
      (∀ child ∈ children, AssignmentPattern.Admitted child) → AssignmentPattern.Admitted (.sequence children)

end Silmaril.Languages.Starlark.Functions.Comprehensions
