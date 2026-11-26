module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Soundness.Thms

/-! # Shared-tensor model contract for opt-in branch binding

The single-branch equation uses the central unit comparison. The full
contextual closure uses coherent region typing and equality-induced tensor
comparisons in the same strong Elgot Freyd models as the original join.
 -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u₁ u₂ v₁ v₂

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Centrality of the Freyd unit gives the typed branch equation, including effects. -/
theorem branch_sound {a : Tm Φ} {ℓ : Nat} {A : τ} (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) :
    denoteRegion J M (.br hℓ ha) = denoteRegion J M (.let₁ ha (.br hℓ (.var (i := 0) rfl))) :=
  denoteRegion_branchBind J M (FreydCategory.CentralUnit.unit_central (J := J)) hℓ ha

/-- The exact shared-tensor model contract of the original join suffices. -/
theorem eqv_sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    (h : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  have hu := FreydCategory.CentralUnit.unit_central (J := J)
  exact (denoteRegion_bindBranchArguments J M hu hr).trans
    ((WithProjectionReturnsAndUnitEta.eqv_sound J M shared (eqv_normalize h)
      hr.bindBranchArguments.hasType hs.bindBranchArguments.hasType).trans
      (denoteRegion_bindBranchArguments J M hu hs).symm)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
