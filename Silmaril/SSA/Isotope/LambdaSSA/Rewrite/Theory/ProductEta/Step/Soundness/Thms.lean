module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Thms

/-! # Soundness of the variable product η generator -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.ProductEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Both sides have the same structural arrow. The scrutinee denotes a
value map, so there is no additional central-unit premise. -/
theorem Step.denotes (h : Step Γ r s L) :
    ∃ f, RegionDenotes J M h.typed.1 f ∧ RegionDenotes J M h.typed.2 f := by
  cases h with
  | let₂Eta hi hℓ => exact ⟨_, RegionDenotes.let₂_br_eta_of_map J M hℓ (.var hi), .br (.var hi)⟩

/-- A variable product η step preserves chosen denotations in coherent models. -/
theorem Step.sound [RegionTypingCoherent (Φ := Φ) J M] (h : Step Γ r s L)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, dr, ds⟩ := h.denotes J M
  exact (dr.eq_denote J M).symm.trans (ds.eq_denote J M)

end Silmaril.Isotope.LambdaSSA.Region.ProductEta
