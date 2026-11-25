module

public import Silmaril.Languages.Starlark.Functions.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

/-- Resolved expressions that can nest calls, branch, or short-circuit.
An atom uses the existing call-free collection expression language. -/
inductive Expr where
  | atom (expression : Lists.Expr)
  | call (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
      (star starStar : Option Expr)
  | branch (test yes no : Expr)
  | logical (op : LogicalOp) (left right : Expr)

@[expose] def callValue : Lists.Iteration.Flow → Lists.Value
  | .returned value => value
  | _ => .scalar .none

@[expose] def Expr.callPos (callee : Expr) (positional : List Expr) : Expr :=
  .call callee positional [] none none

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

end Silmaril.Languages.Starlark.Functions.Lowering
