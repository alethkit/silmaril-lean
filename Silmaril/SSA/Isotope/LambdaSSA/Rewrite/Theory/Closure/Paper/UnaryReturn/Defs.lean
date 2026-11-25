module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs

/-! # Standalone unary return fusion -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn

open Paper.RetainedLet (returnOnce)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Fuse two unary binders immediately before forwarding the result.
This is the singleton-return instance, in the reverse direction, of the
companion's `Region.Eqv.let1_let1`. Its weakened continuation keeps the
newest variable unchanged in this instance.

[Companion declaration](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Eqv.lean#L964-L973). -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | fuse {Γ : VCtx τ} {A D : τ} {a b : Tm Φ}
      (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D) :
      Step Γ (.let₁ a (returnOnce b)) (returnOnce (.let₁ a b)) [D]

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {D : τ} {t : Tm Φ}

theorem returnOnce_valueBranches (ht : Tm.HasType Γ t D) : ValueBranches Γ (returnOnce t) [D] :=
  .let₁ ht (.br (ℓ := 0) rfl (.var (i := 0) rfl))

/-- Both endpoints already have constructor-valued branch arguments. -/
theorem Step.valueBranches (e : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases e with
  | fuse ha hb => exact ⟨.let₁ ha (returnOnce_valueBranches hb), returnOnce_valueBranches (.let₁ ha hb)⟩

theorem Step.typed (e : Step Γ r s L) : HasType Γ r L ∧ HasType Γ s L :=
  ⟨e.valueBranches.1.hasType, e.valueBranches.2.hasType⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn
