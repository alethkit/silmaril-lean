module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Forgetting an unused value context in categorical control -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst snd lift)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (retainEnvironment retainEnvironment_comp retainEnvironment_map routeEnvironment)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate extend retainLeft splitMapCoprod)

universe v w u z

variable {V : Type u} {C : Type z} [Category.{v} V] [Category.{w} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

section Distributive

variable [DistributiveFreydCategory J]

@[reassoc] theorem split_inl (A B : V) :
    J.map (coprod.inl : A ⟶ A ⨿ B) ≫ splitMapCoprod J A B = coprod.inl :=
  map_inl_inv_coprodComparison J

@[reassoc] theorem split_inr (A B : V) :
    J.map (coprod.inr : B ⟶ A ⨿ B) ≫ splitMapCoprod J A B = coprod.inr :=
  map_inr_inv_coprodComparison J

@[reassoc] private theorem route_inl (R A B : V) :
    J.map (R ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ routeEnvironment J R A B = coprod.inl := by
  have h : (R ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv =
      coprod.inl := by
    apply (cancel_mono (DistributiveTensor.leftIso R A B).hom).1
    simp [DistributiveTensor.leftIso]
  rw [routeEnvironment, ← J.map_comp_assoc, h, split_inl]

@[reassoc] private theorem route_inr (R A B : V) :
    J.map (R ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ routeEnvironment J R A B = coprod.inr := by
  have h : (R ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso R A B).hom).1
    simp [DistributiveTensor.leftIso]
  rw [routeEnvironment, ← J.map_comp_assoc, h, split_inr]

@[reassoc] private theorem route_drop (R A B : V) :
    routeEnvironment J R A B ≫ coprod.map (J.map (snd R A)) (J.map (snd R B)) =
      J.map (snd R (A ⨿ B)) ≫ splitMapCoprod J A B := by
  let d := (DistributiveTensor.leftIso R A B).hom
  apply (cancel_epi (coprodComparison J (R ⊗ A) (R ⊗ B) ≫ J.map d)).mp
  apply coprod.hom_ext
  · have left : (coprod.inl : J.obj (R ⊗ A) ⟶ _) ≫
        (coprodComparison J (R ⊗ A) (R ⊗ B) ≫ J.map d) =
        J.map (R ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      simp [d, DistributiveTensor.leftIso, ← J.map_comp]
    rw [← Category.assoc, left, route_inl_assoc, coprod.inl_map]
    rw [← Category.assoc, left, ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_snd,
      J.map_comp, Category.assoc, split_inl]
  · have right : (coprod.inr : J.obj (R ⊗ B) ⟶ _) ≫
        (coprodComparison J (R ⊗ A) (R ⊗ B) ≫ J.map d) =
        J.map (R ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      simp [d, DistributiveTensor.leftIso, ← J.map_comp]
    rw [← Category.assoc, right, route_inr_assoc, coprod.inr_map]
    rw [← Category.assoc, right, ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_snd,
      J.map_comp, Category.assoc, split_inr]

@[reassoc] private theorem retain_drop [FreydCategory.CentralUnit J] {R A B : V}
    (f : J.obj A ⟶ J.obj B) :
    retainLeft J (R := R) f ≫ J.map (snd R B) = J.map (snd R A) ≫ f := by
  simpa [retainLeft, CategoryTheory.PremonoidalCategory.leftTensor] using
    FreydCategory.whiskerLeft_snd J R f

@[reassoc] private theorem extend_drop [FreydCategory.CentralUnit J] {R A : V}
    (f : J.obj R ⟶ J.obj A) :
    extend J f ≫ J.map (snd R A) = f := by
  change (J.map (duplicate R) ≫ retainLeft J (R := R) f) ≫ _ = _
  simp only [Category.assoc, retain_drop, ← J.map_comp_assoc, duplicate,
    CartesianMonoidalCategory.lift_snd, J.map_id, Category.id_comp]

theorem case_project [FreydCategory.CentralUnit J] {R A B D : V}
    (f : J.obj R ⟶ J.obj (A ⨿ B)) (l : J.obj A ⟶ J.obj D) (r : J.obj B ⟶ J.obj D) :
    caseWithContext J f (J.map (snd R A) ≫ l) (J.map (snd R B) ≫ r) =
      f ≫ splitMapCoprod J A B ≫ coprod.desc l r := by
  have eq :
      coprod.desc (J.map (snd R A) ≫ l) (J.map (snd R B) ≫ r) =
        coprod.map (J.map (snd R A)) (J.map (snd R B)) ≫ coprod.desc l r := by
    apply coprod.hom_ext <;> simp
  have unfoldCase : caseWithContext J f (J.map (snd R A) ≫ l) (J.map (snd R B) ≫ r) =
      extend J f ≫ routeEnvironment J R A B ≫
        coprod.desc (J.map (snd R A) ≫ l) (J.map (snd R B) ≫ r) := by
    simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, routeEnvironment, Category.assoc]
  rw [unfoldCase]
  simp only [eq, route_drop_assoc, extend_drop_assoc]

end Distributive

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem loop_project {R A B : V} (f : J.obj A ⟶ J.obj (B ⨿ A)) :
    contextualLoop J (J.map (snd R A) ≫ f) =
      J.map (snd R A) ≫ iterate (f ≫ splitMapCoprod J B A) := by
  let body := retainLeft J (R := R) f ≫ routeEnvironment J R B A
  have unfoldLoop : contextualLoop J (J.map (snd R A) ≫ f) =
      iterate (retainEnvironment J (fst R A) (J.map (snd R A) ≫ f) ≫
        routeEnvironment J R B A) ≫ J.map (snd R B) := by
    simp only [contextualLoop, retainEnvironment, routeEnvironment, Category.assoc]
  rw [unfoldLoop]
  rw [retainEnvironment_comp, retainEnvironment_map]
  have h : lift (fst R A) (snd R A) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h, J.map_id, Category.id_comp, ElgotCategory.naturality]
  change iterate (body ≫ coprod.map (J.map (snd R B)) (𝟙 (J.obj (R ⊗ A)))) = _
  apply ElgotFreydCategory.pure_uniformity J _ _ (snd R A)
  have hmap : coprod.map (J.map (snd R B)) (𝟙 (J.obj (R ⊗ A))) ≫
      coprod.map (𝟙 (J.obj B)) (J.map (snd R A)) =
      coprod.map (J.map (snd R B)) (J.map (snd R A)) := by
    apply coprod.hom_ext <;> simp
  simp only [body, Category.assoc, hmap]
  rw [route_drop, retain_drop_assoc]

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs
