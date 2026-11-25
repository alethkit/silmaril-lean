module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBetaSoundness

/-! # Denotational soundness of the opt-in constructor-pair equation -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Region.ProductBeta

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
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

/-- The constructor-pair equation has a common structural denotation.
The components are pure value arrows in the exact typing model. -/
theorem Step.denotes
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L) :
    ∃ f, RegionDenotes J M h.typed.1 f ∧ RegionDenotes J M h.typed.2 f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta.step_denotes J M h

/-- A constructor-pair step preserves the chosen region denotation. -/
theorem Step.sound [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Step Γ r s L)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, dr, ds⟩ := h.denotes J M
  exact (dr.eq_denote J M).symm.trans (ds.eq_denote J M)

/-- The opt-in equivalence has the model premises of the existing CFG η
soundness theorem. -/
theorem Eqv.sound_sharedTensor
    [RegionTypingCoherent (Φ := Φ) J M]
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductBeta.eqv_sound_sharedTensor J M hu shared h hr hs

end Silmaril.Isotope.LambdaSSA.Region.ProductBeta
