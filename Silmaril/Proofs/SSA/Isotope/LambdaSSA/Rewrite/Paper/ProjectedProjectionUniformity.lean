module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.Defs
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Coherence.Thms

/-! # Projection squares for guarded iteration in the case-return quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProjectionUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open CartesianMonoidalCategory (snd)
universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
local notation "Val" => ValueCategory (τ := τ) (Φ := Φ) pe
local notation "J" => inclusion (τ := τ) (Φ := Φ) pe

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive
attribute [local instance] Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.guardedIteration


theorem uniformity_fst_unit {B : Comp} (A : τ)
    (f : tensorObj Seed (ofType Seed A) (ofType Seed (Silmaril.unit : τ)) ⟶
      B ⨿ tensorObj Seed (ofType Seed A) (ofType Seed (Silmaril.unit : τ)))
    (g : ofType Seed A ⟶ B ⨿ ofType Seed A)
    (_square : f ≫ coprod.map (𝟙 B) (productFst Seed A Silmaril.unit) =
      productFst Seed A Silmaril.unit ≫ g) :
    iterateChosen Seed f = productFst Seed A Silmaril.unit ≫ iterateChosen Seed g :=
  uniformity_of_iso Seed
    (rightUnitIsoOfEta Seed (unit_eta_of_include Seed (Paper.WithCaseReturns.includeUnit pe)) (ofType Seed A))
    f g _square

theorem uniformity_snd_unit {B : Comp} (A : τ)
    (f : tensorObj Seed (ofType Seed (Silmaril.unit : τ)) (ofType Seed A) ⟶
      B ⨿ tensorObj Seed (ofType Seed (Silmaril.unit : τ)) (ofType Seed A))
    (g : ofType Seed A ⟶ B ⨿ ofType Seed A)
    (_square : f ≫ coprod.map (𝟙 B) (productSnd Seed Silmaril.unit A) =
      productSnd Seed Silmaril.unit A ≫ g) :
    iterateChosen Seed f = productSnd Seed Silmaril.unit A ≫ iterateChosen Seed g :=
  uniformity_of_iso Seed
    (leftUnitIsoOfEta Seed (unit_eta_of_include Seed (Paper.WithCaseReturns.includeUnit pe)) (ofType Seed A))
    f g _square

set_option backward.isDefEq.respectTransparency false in
private theorem snd_natural (R : Val) {A B : Val} (f : (J).obj A ⟶ (J).obj B) :
    ((J).obj R ◁ f) ≫ (J).map (snd R B) = (J).map (snd R A) ≫ f := by
  let := freyd (τ := τ) (Φ := Φ) pe
  let := centralUnit (τ := τ) (Φ := Φ) pe
  have e := FreydCategory.whiskerLeft_snd (J) R f
  obtain ⟨hA, eA⟩ := sharedTensor pe R A
  obtain ⟨hB, eB⟩ := sharedTensor pe R B
  have hA_eq : hA = rfl := Subsingleton.elim _ _
  have hB_eq : hB = rfl := Subsingleton.elim _ _
  rw [eA, eB, hA_eq, hB_eq] at e
  simpa only [eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp] using e

private def projSnd (R A : Comp) : (R ⊗ A) ⟶ A :=
  productSnd Seed R.as A.as

private theorem projSnd_natural (R : Comp) {A B : Comp} (f : A ⟶ B) :
    (R ◁ f) ≫ (projSnd pe R B) = (projSnd pe R A) ≫ f :=
  snd_natural pe (⟨R⟩ : Val) (A := ⟨A⟩) (B := ⟨B⟩) f

set_option backward.isDefEq.respectTransparency false in
theorem retained_snd (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    iterateChosen Seed (retainLeftStep pe R g) =
      productSnd Seed R.as A.as ≫ iterateChosen Seed g := by
  change iterateChosen Seed (((R ◁ g) ≫ DistributivePremonoidalCategory.leftInv R B A) ≫
    coprod.map (projSnd pe R B) (𝟙 (R ⊗ A))) = projSnd pe R A ≫ iterateChosen Seed g
  rw [← iterateChosen_naturality]
  change CategoryTheory.iterate ((R ◁ g) ≫ DistributivePremonoidalCategory.leftInv R B A) ≫
    (projSnd pe R B) = _
  rw [iterate_whiskerLeft pe]
  exact projSnd_natural pe R (iterateChosen Seed g)

set_option backward.isDefEq.respectTransparency false in
theorem retained_snd_square (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    retainLeftStep pe R g ≫ coprod.map (𝟙 B) (productSnd Seed R.as A.as) =
      productSnd Seed R.as A.as ≫ g := by
  change (((R ◁ g) ≫ DistributivePremonoidalCategory.leftInv R B A) ≫
    coprod.map (projSnd pe R B) (𝟙 (R ⊗ A))) ≫ coprod.map (𝟙 B) (projSnd pe R A) =
      projSnd pe R A ≫ g
  have router :
      (DistributiveTensor.leftIso R B A).hom ≫ projSnd pe R (B ⨿ A) =
        coprod.map (projSnd pe R B) (projSnd pe R A) := by
    apply coprod.hom_ext
    · rw [coprod.inl_map, ← Category.assoc]
      change (coprod.inl ≫ DistributiveTensor.leftHom R B A) ≫ _ = _
      rw [DistributiveTensor.inl_leftHom, projSnd_natural]
    · rw [coprod.inr_map, ← Category.assoc]
      change (coprod.inr ≫ DistributiveTensor.leftHom R B A) ≫ _ = _
      rw [DistributiveTensor.inr_leftHom, projSnd_natural]
  have route :
      coprod.map (projSnd pe R B) (𝟙 (R ⊗ A)) ≫ coprod.map (𝟙 B) (projSnd pe R A) =
        coprod.map (projSnd pe R B) (projSnd pe R A) := by
    rw [coprod.map_map, Category.comp_id, Category.id_comp]
  simp only [Category.assoc, route]
  rw [← router]
  change (R ◁ g) ≫ (DistributiveTensor.leftIso R B A).inv ≫
    (DistributiveTensor.leftIso R B A).hom ≫ projSnd pe R (B ⨿ A) = _
  rw [Iso.inv_hom_id_assoc, projSnd_natural]

set_option backward.isDefEq.respectTransparency false in
private theorem braid_snd (A R : Comp) :
    (braidIso Seed A R).hom ≫ (projSnd pe R A) = productFst Seed A.as R.as := by
  change (projection Seed).map (Paper.TypeCategory.braid (show τ from A.as) (show τ from R.as)) ≫ _ = _
  rw [Paper.TypeCategory.braid_eq_pair, map_pairArrows]
  exact pairing_snd_of_discard Seed _ _ (snd_discard Seed A.as R.as)

set_option backward.isDefEq.respectTransparency false in
theorem retained_fst (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    iterateChosen Seed (retainRightStep pe R g) =
      productFst Seed A.as R.as ≫ iterateChosen Seed g := by
  have commute : retainRightStep pe R g ≫ coprod.map (𝟙 B) (braidIso Seed A R).hom =
      (braidIso Seed A R).hom ≫ retainLeftStep pe R g := by
    simp only [retainRightStep, Category.assoc, coprod.map_map, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id]
  rw [uniformity_of_iso Seed (braidIso Seed A R) _ _ commute, retained_snd pe]
  change (braidIso Seed A R).hom ≫ projSnd pe R A ≫ iterateChosen Seed g = _
  rw [← Category.assoc, braid_snd]

set_option backward.isDefEq.respectTransparency false in
theorem retained_fst_square (R : Comp) {A B : Comp} (g : A ⟶ B ⨿ A) :
    retainRightStep pe R g ≫ coprod.map (𝟙 B) (productFst Seed A.as R.as) =
      productFst Seed A.as R.as ≫ g := by
  have route : coprod.map (𝟙 B) (braidIso Seed A R).inv ≫ coprod.map (𝟙 B) (productFst Seed A.as R.as) =
      coprod.map (𝟙 B) (projSnd pe R A) := by
    rw [coprod.map_map, Category.id_comp, ← braid_snd pe, Iso.inv_hom_id_assoc]
  change ((braidIso Seed A R).hom ≫ retainLeftStep pe R g ≫ _) ≫ _ = _
  have square : retainLeftStep pe R g ≫ coprod.map (𝟙 B) (projSnd pe R A) =
      projSnd pe R A ≫ g := retained_snd_square pe R g
  rw [Category.assoc, Category.assoc, route, square, ← Category.assoc, braid_snd]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedProjectionUniformity
