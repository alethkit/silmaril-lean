module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ContextualProductEta

/-! # Contextual variable product η for exactly typed Paper regions -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {i : Nat} {A B : τ}

/-- Unpack a product variable and reinsert its rebuilt pair into an exactly
typed continuation. The variable η producer has constructor-valued branches. -/
theorem product_variable_eta_context (hi : At Γ i (product A B)) (hr : HasType Γ r L) :
    Eqv Γ (.let₂ (.var i) (r.substVars (splitProduct i))) r L :=
  ContextualProductEta.product_variable_eta_context hi hr

/-- Equality after replacing a typed product variable by its two unpacked
components is equivalent to equality in the original context. -/
theorem product_variable_eta_iff (hi : At Γ i (product A B)) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Eqv (B :: A :: Γ) (r.substVars (splitProduct i)) (s.substVars (splitProduct i)) L ↔
      Eqv Γ r s L :=
  ContextualProductEta.product_variable_eta_iff hi hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper
