module

public import Silmaril.SSA.RVSDG.Categorical.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst snd lift)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (retainLeft caseWithContext contextualLoop splitMapCoprod)

set_option backward.isDefEq.respectTransparency false

universe d h c k
variable {D : Type d} {C : Type c} [Category.{h} D] [Category.{k} C]
  [CartesianMonoidalCategory D] [SymmetricCategory D]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts D] [HasFiniteCoproducts C]
  [DistributiveTensor D] [DistributivePremonoidalCategory C]

variable (J : D ⥤ C)

local notation "split" => splitMapCoprod J

section Pure

variable [DistributiveFreydCategory J]

private theorem retain_map (R : D) {X Y : D} (f : X ⟶ Y) :
    retainLeft J (R := R) (J.map f) = J.map (R ◁ f) := by
  simp only [retainLeft, CategoryTheory.PremonoidalCategory.leftTensor,
    CategoryTheory.PremonoidalCategory.id_whiskerRight, Category.id_comp,
    Functor.StrongPremonoidal.tensor_naturality_right]
  simp

private theorem extend_map {X Y : D} (f : X ⟶ Y) :
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend J (J.map f) = J.map (lift (𝟙 X) f) := by
  change J.map (lift (𝟙 X) (𝟙 X)) ≫ retainLeft J (J.map f) = _
  rw [retain_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

private theorem copair_map {X Y Z : D} (l : X ⟶ Z) (r : Y ⟶ Z) :
    split X Y ≫ coprod.desc (J.map l) (J.map r) = J.map (coprod.desc l r) := by
  apply (cancel_epi (coprodComparison J X Y)).1
  simp only [splitMapCoprod, IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext <;> simp [← J.map_comp]

theorem map_split {A B X Y : D} (p : A ⟶ X) (q : B ⟶ Y) :
    split A B ≫ coprod.map (J.map p) (J.map q) =
      J.map (coprod.map p q) ≫ split X Y :=
  (coprodComparison_inv_natural J p q).symm

omit [SymmetricCategory D] in
private theorem proj_dist {R X Y Z : D} (p : X ⟶ Z) (q : Y ⟶ Z) :
    (DistributiveTensor.leftIso R X Y).inv ≫ coprod.desc (snd R X ≫ p) (snd R Y ≫ q) =
      snd R (X ⨿ Y) ≫ coprod.desc p q := by
  apply (cancel_epi (DistributiveTensor.leftIso R X Y).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply coprod.hom_ext <;> simp [DistributiveTensor.leftIso]

theorem case_project {E X Y Z : D} (f : E ⟶ X ⨿ Y) (p : X ⟶ Z) (q : Y ⟶ Z) :
    caseWithContext J (J.map f) (J.map (snd E X ≫ p)) (J.map (snd E Y ≫ q)) =
      J.map (f ≫ coprod.desc p q) := by
  unfold caseWithContext Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  simp only [extend_map, copair_map]
  rw [← J.map_comp (DistributiveTensor.leftIso E X Y).inv, proj_dist,
    ← J.map_comp, ← Category.assoc, CartesianMonoidalCategory.lift_snd]

theorem case_right {E X Y Z : D} (f : E ⟶ Y)
    (p : J.obj (E ⊗ X) ⟶ J.obj Z) (q : J.obj (E ⊗ Y) ⟶ J.obj Z) :
    caseWithContext J (J.map (f ≫ (coprod.inr : Y ⟶ X ⨿ Y))) p q =
      J.map (lift (𝟙 E) f) ≫ q := by
  have lifted : lift (𝟙 E) (f ≫ (coprod.inr : Y ⟶ X ⨿ Y)) =
      lift (𝟙 E) f ≫ (E ◁ coprod.inr) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have distrib : (E ◁ (coprod.inr : Y ⟶ X ⨿ Y)) ≫ (DistributiveTensor.leftIso E X Y).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E X Y).hom).1
    simp [DistributiveTensor.leftIso]
  unfold caseWithContext Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [extend_map, lifted]
  simp only [J.map_comp, Category.assoc]
  rw [← J.map_comp_assoc (E ◁ (coprod.inr : Y ⟶ X ⨿ Y)), distrib]
  unfold splitMapCoprod
  rw [map_inr_inv_coprodComparison_assoc, coprod.inr_desc]

end Pure

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- A read-only context that the body ignores can be projected out of its iteration. -/
theorem contextual_project {E X Y : D} (f : X ⟶ Y ⨿ X) :
    contextualLoop J (J.map (snd E X ≫ f)) =
      J.map (snd E X) ≫ iterate (J.map f ≫ split Y X) := by
  let q : E ⊗ X ⟶ (E ⊗ Y) ⨿ (E ⊗ X) :=
    (lift (fst E X) (𝟙 (E ⊗ X)) ≫ (E ◁ (snd E X ≫ f))) ≫
      (DistributiveTensor.leftIso E Y X).inv
  have projected : q ≫ coprod.map (snd E Y) (snd E X) = snd E X ≫ f := by
    unfold q
    simp only [Category.assoc]
    have cases : coprod.map (snd E Y) (snd E X) =
        coprod.desc (snd E Y ≫ coprod.inl) (snd E X ≫ coprod.inr) := by
      apply coprod.hom_ext <;> simp
    rw [cases, proj_dist, CartesianMonoidalCategory.whiskerLeft_snd_assoc,
      CartesianMonoidalCategory.lift_snd_assoc]
    simp
  have projStep : (J.map q ≫ split (E ⊗ Y) (E ⊗ X)) ≫
      coprod.map (J.map (snd E Y)) (J.map (snd E X)) =
        J.map (snd E X) ≫ (J.map f ≫ split Y X) := by
    rw [Category.assoc, map_split, ← J.map_comp_assoc, projected, J.map_comp, Category.assoc]
  unfold contextualLoop
  rw [retain_map, ← J.map_comp_assoc, ← J.map_comp_assoc]
  change iterate (J.map q ≫ split (E ⊗ Y) (E ⊗ X)) ≫ J.map (snd E Y) = _
  rw [ElgotCategory.naturality]
  apply ElgotFreydCategory.pure_uniformity J _ _ (snd E X)
  simp only [Category.assoc, coprod.map_map, Category.comp_id, Category.id_comp]
  simpa only [Category.assoc] using projStep

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs
