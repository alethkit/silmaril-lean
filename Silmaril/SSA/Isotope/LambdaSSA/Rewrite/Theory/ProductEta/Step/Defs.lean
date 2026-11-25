module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # A standalone variable-scrutinee product η step -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ProductEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- Unpacking a product variable and immediately branching on the rebuilt
pair agrees with branching directly on the variable. This is the variable
case of the region form of Figure 16's product η in arXiv:2411.09347v2. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | let₂Eta {Γ : VCtx τ} {L : LCtx τ} {i ℓ : Nat} {A B : τ}
      (hi : At Γ i (Silmaril.product A B)) (hℓ : At L ℓ (Silmaril.product A B)) :
      Step Γ (.let₂ (.var i) (.br ℓ (.pair (.var 1) (.var 0)))) (.br ℓ (.var i)) L

end Silmaril.Isotope.LambdaSSA.Region.ProductEta
