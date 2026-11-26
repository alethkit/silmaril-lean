module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.InputPacking.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Thms

/-! # Input records and tagged exits in the same categorical interpretation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedInputPackingDenotation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProjectionReturnsAndUnitEta
open Paper.WithProjectionReturnsAndUnitEta.InputPacking
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

set_option backward.isDefEq.respectTransparency false in
include shared in
theorem denoteRegion_packInputsDestructure (hr : HasType Γ r L) :
    denoteRegion J M hr.packInputsDestructure =
      J.map (packedInputIso M Γ).inv ≫ denoteRegion J M hr := by
  have h := eqv_sound J M shared (unpack_pack hr) hr.packInputsDestructure.unpackInputs hr
  rw [denoteRegion_unpackInputs J M] at h
  rw [← h, ← J.map_comp_assoc, Iso.inv_hom_id, J.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem denote_packedRegion (hr : ValueBranches Γ r L) :
    denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hr)) =
      J.map (inputRecordIso M Γ).inv ≫ denoteRegion J M hr.hasType ≫ J.map (packLabel M L) := by
  rw [packedRegionEquiv_apply, ExitPacking.denote_packArrow J M shared,
    denoteRegion_packInputsDestructure J M shared hr.hasType]
  have coord : ((λ_ (M.obj (packedInputType Γ))).inv : _ ⟶ ctxObj M [packedInputType Γ]) ≫
      (packedInputIso M Γ).inv = (inputRecordIso M Γ).inv := by
    simp only [packedInputIso, Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, ← J.map_comp_assoc, coord]

set_option backward.isDefEq.respectTransparency false in
theorem denote_packedRegion_eq_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hr)) =
        denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hs)) ↔
      denoteRegion J M hr.hasType = denoteRegion J M hs.hasType := by
  rw [packedRegionEquiv_apply, packedRegionEquiv_apply,
    ExitPacking.denote_packArrow_eq_iff J M shared,
    denoteRegion_packInputsDestructure J M shared, denoteRegion_packInputsDestructure J M shared,
    cancel_epi]

set_option backward.isDefEq.respectTransparency false in
theorem denote_packedBoundRegion_eq_iff (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hr.bindBranchArguments)) =
        denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hs.bindBranchArguments)) ↔
      denoteRegion J M hr = denoteRegion J M hs := by
  let hu := FreydCategory.CentralUnit.unit_central (J := J)
  rw [denote_packedRegion_eq_iff J M shared,
    ← denoteRegion_bindBranchArguments J M hu hr, ← denoteRegion_bindBranchArguments J M hu hs]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedInputPackingDenotation
