module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Values.Product.Thms

/-! # The discard-preserving subcategory of projected copying values -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.unit : τ)

/-- Projected copying values whose literal discard is natural at this arrow. -/
def DiscardPreservingReturn : MorphismProperty (TypeCategory Seed) := fun X A f =>
  ProjectedCopyingReturn Seed pe f ∧ f ≫ discardArrow Seed A.as = discardArrow Seed X.as

instance discardPreservingReturn_multiplicative : (DiscardPreservingReturn Seed pe).IsMultiplicative where
  id_mem X := ⟨(ProjectedCopyingReturn Seed pe).id_mem X, Category.id_comp _⟩
  comp_mem f g hf hg := ⟨(ProjectedCopyingReturn Seed pe).comp_mem f g hf.1 hg.1,
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hg.2).trans hf.2)⟩

abbrev DiscardPreservingValueCategory := WideSubcategory (DiscardPreservingReturn Seed pe)

set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory Seed pe

variable (includeProjection : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
  WithProjectionReturns.Step Γ r s L → Seed Γ r s L)

def discardPreservingFan (A B : τ) : BinaryFan (⟨Obj A⟩ : Values) (⟨Obj B⟩ : Values) :=
  BinaryFan.mk (P := (⟨Obj (product A B)⟩ : Values))
    ⟨productFst Seed A B, WithProjectionReturns.fst_mem pe Seed includeProjection A B, fst_discard Seed A B⟩
    ⟨productSnd Seed A B, WithProjectionReturns.snd_mem pe Seed includeProjection A B, snd_discard Seed A B⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
