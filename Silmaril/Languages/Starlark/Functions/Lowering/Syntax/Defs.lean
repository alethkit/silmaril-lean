module

public import Silmaril.Languages.Starlark.Functions.Arguments.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

@[expose] def callValue : Lists.Iteration.Flow → Lists.Value
  | .returned value => value
  | _ => .scalar .none

/-- The resolved grammar fixes operand order independently of call binding. -/
@[expose] def argumentExprs (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) : List Expr :=
  positional ++ keywords.map Prod.snd ++ star.toList ++ starStar.toList

@[expose] def argumentShape (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) : ArgumentShape :=
  ⟨positional.length, keywords.map Prod.fst, star.isSome, starStar.isSome⟩

theorem argumentSize (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) {part : Expr}
    (member : part ∈ argumentExprs positional keywords star starStar) :
    sizeOf part < sizeOf (.call callee positional keywords star starStar : Expr) := by
  simp only [argumentExprs, List.mem_append] at member
  rcases member with ((pos | named) | spread) | mapping
  · have := List.sizeOf_lt_of_mem pos
    simp
    omega
  · obtain ⟨⟨name, value⟩, inKeywords, rfl⟩ := List.mem_map.mp named
    have := List.sizeOf_lt_of_mem inKeywords
    simp at this ⊢
    omega
  · obtain rfl := Option.mem_toList.mp spread
    simp
    omega
  · obtain rfl := Option.mem_toList.mp mapping
    simp
    omega

/-- Check explicit keyword names at every call, including unreachable operands. -/
@[expose] def Expr.validateCalls : Expr → Except CallStaticError Unit
  | .atom _ => .ok ()
  | .call callee positional keywords star starStar => do
    if let some duplicate := firstDuplicate (keywords.map Prod.fst) then
      throw (.duplicateExplicitKeyword duplicate)
    callee.validateCalls
    (argumentExprs positional keywords star starStar).attach.forM fun operand => do
      have := argumentSize callee positional keywords star starStar operand.property
      operand.val.validateCalls
  | .branch test yes no => do
    test.validateCalls
    yes.validateCalls
    no.validateCalls
  | .logical _ left right => do
    left.validateCalls
    right.validateCalls
termination_by expression => sizeOf expression
decreasing_by all_goals first | assumption | (simp_wf; omega)

end Silmaril.Languages.Starlark.Functions.Lowering
