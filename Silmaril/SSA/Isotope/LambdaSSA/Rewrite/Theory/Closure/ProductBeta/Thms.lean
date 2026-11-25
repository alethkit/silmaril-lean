module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta

/-! # Exact typing and unary-let form of constructor-pair β -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ProductBeta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem Eqv.cfgEta (h : CfgEta.Eqv Γ r s L) : Eqv Γ r s L :=
  .single (.inl (.inl h))

theorem Eqv.ofStep (h : Step Γ r s L) : Eqv Γ r s L :=
  .single (.inl (.inr h))

theorem Eqv.symm (h : Eqv Γ r s L) : Eqv Γ s r L :=
  Std.Symm.symm _ _ h

theorem Step.typed (h : Step Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta.step_typed h

theorem Eqv.typed (h : Eqv Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta.eqv_typed h

/-- Destructuring a constructor pair agrees with binding its two
components in order. The right component is weakened under the left binder. -/
theorem Eqv.let₂_pair {A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B)
    (hr : Region.HasType (B :: A :: Γ) r L) :
    Eqv Γ (.let₂ (.pair a b) r) (.let₁ a (.let₁ (b.rename Nat.succ) r)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta.let₂_pair ha hb hr

end Silmaril.Isotope.LambdaSSA.Region.ProductBeta
