module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality

/-! # Retaining a value environment across sequential computations -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext duplicate extend retainLeft splitMapCoprod)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "fst" => CartesianMonoidalCategory.fst
local notation "snd" => CartesianMonoidalCategory.snd
local notation "lift" => CartesianMonoidalCategory.lift

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

local notation "tIso" => Functor.StrongPremonoidal.tensorIso (J := J)

private theorem retainLeft_whisker {R A B : V} (f : J.obj A ⟶ J.obj B) :
    retainLeft J (R := R) f = (tIso R A).inv ≫ J.obj R ◁ f ≫ (tIso R B).hom := by
  simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp]

theorem retainLeft_copy {E A B : V} (f : J.obj A ⟶ J.obj B)
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv)) :
    J.map ((duplicate E ▷ A) ≫ (α_ E E A).hom) ≫
      retainLeft J (R := E) (retainLeft J (R := E) f) =
    retainLeft J (R := E) f ≫ J.map ((duplicate E ▷ B) ≫ (α_ E E B).hom) := by
  let d := J.map (duplicate E) ≫ (tIso E E).inv
  have transport (X : V) :
      (tIso E X).hom ≫ J.map ((duplicate E ▷ X) ≫ (α_ E E X).hom) =
        (d ▷ J.obj X) ≫ (α_ (J.obj E) (J.obj E) (J.obj X)).hom ≫
          J.obj E ◁ (tIso E X).hom ≫ (tIso E (E ⊗ X)).hom := by
    rw [J.map_comp, ← Category.assoc, ← Functor.StrongPremonoidal.tensor_naturality_left,
      Category.assoc]
    have h := Functor.StrongPremonoidal.associativity (J := J) E E X
    simp only [d, comp_whiskerRight, Category.assoc]
    rw [h]
    rw [← comp_whiskerRight_assoc (tIso E E).inv, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp]
  apply (cancel_epi (tIso E A).hom).mp
  simp only [Category.assoc, retainLeft_whisker, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (transport A), transport B]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, whiskerLeft_comp]
  rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp,
    ← associator_naturality_right_assoc]
  have slide := central.1 f
  change (d ▷ J.obj A) ≫ (J.obj E ⊗ J.obj E) ◁ f =
    J.obj E ◁ f ≫ d ▷ J.obj B at slide
  rw [reassoc_of% slide]

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
private theorem copyValue (E A : V) :
    (duplicate E ▷ A) ≫ (α_ E E A).hom = lift (fst E A) (𝟙 (E ⊗ A)) := by
  have h : duplicate E ▷ A = lift (lift (fst E A) (fst E A)) (snd E A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
  rw [h, CartesianMonoidalCategory.lift_lift_associator_hom]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc] theorem extend_capture {E A : V} (f : J.obj E ⟶ J.obj A)
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv)) :
    J.map (duplicate E) ≫ retainLeft J (R := E) (extend J f) =
      extend J f ≫ J.map (lift (fst E A) (𝟙 (E ⊗ A))) := by
  have same : duplicate E ≫ E ◁ duplicate E =
      duplicate E ≫ (duplicate E ▷ E) ≫ (α_ E E E).hom := by
    rw [copyValue]
    apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]
  simp only [extend_eq_retainLeft, retainLeft_comp, retainLeft_map, Category.assoc]
  rw [← J.map_comp_assoc, same, J.map_comp_assoc]
  rw [retainLeft_copy J f central, copyValue]

theorem bind_assoc_capture {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (f : J.obj E ⟶ J.obj A) (g : J.obj (E ⊗ A) ⟶ J.obj B)
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (bindArrow J f g) k =
      bindArrow J f (bindArrow J g (J.map (fst E A ▷ B) ≫ k)) := by
  have prepare : duplicate (E ⊗ A) ≫ fst E A ▷ (E ⊗ A) =
      lift (fst E A) (𝟙 (E ⊗ A)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        duplicate, CartesianMonoidalCategory.lift_fst_assoc, Category.id_comp,
        CartesianMonoidalCategory.lift_fst]
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        duplicate, CartesianMonoidalCategory.lift_snd]
  change extend J (extend J f ≫ g) ≫ k = extend J f ≫ extend J g ≫ J.map (fst E A ▷ B) ≫ k
  have lhs : extend J (extend J f ≫ g) =
      J.map (duplicate E) ≫ retainLeft J (R := E) (extend J f) ≫ retainLeft J (R := E) g := by
    rw [extend_eq_retainLeft, retainLeft_comp]
  rw [lhs, Category.assoc, Category.assoc, extend_capture_assoc J f central]
  simp only [extend_eq_retainLeft J g, Category.assoc]
  rw [← retainLeft_pre_assoc, ← J.map_comp_assoc, prepare]

theorem bind_assoc_reindex {E A X B D : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (f : J.obj E ⟶ J.obj A) (p : E ⊗ A ⟶ X)
    (g : J.obj X ⟶ J.obj B) (q : X ⟶ E) (hq : p ≫ q = fst E A)
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (bindArrow J f (J.map p ≫ g)) k =
      bindArrow J f (J.map p ≫ bindArrow J g (J.map (q ▷ B) ≫ k)) := by
  rw [bind_assoc_capture J central, ← bind_pre_map, ← J.map_comp_assoc,
    ← MonoidalCategory.comp_whiskerRight, hq]

theorem bind_case_capture {E A B X Y : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (scrutinee : J.obj E ⟶ J.obj (A ⨿ B))
    (left : J.obj (E ⊗ A) ⟶ J.obj X) (right : J.obj (E ⊗ B) ⟶ J.obj X)
    (k : J.obj (E ⊗ X) ⟶ J.obj Y) :
    bindArrow J (caseWithContext J scrutinee left right) k =
      caseWithContext J scrutinee
        (bindArrow J left (J.map (fst E A ▷ X) ≫ k))
        (bindArrow J right (J.map (fst E B ▷ X) ≫ k)) := by
  let route := J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)
  have : IsIso route := by dsimp only [route, splitMapCoprod]; infer_instance
  have case_def (l : J.obj (E ⊗ A) ⟶ J.obj Y) (r : J.obj (E ⊗ B) ⟶ J.obj Y) :
      caseWithContext J scrutinee l r = bindArrow J scrutinee (route ≫ coprod.desc l r) := by
    simp only [caseWithContext, route, Category.assoc]
  have old_def : caseWithContext J scrutinee left right =
      bindArrow J scrutinee (route ≫ coprod.desc left right) := by
    simp only [caseWithContext, route, Category.assoc]
  have route_left : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have route_right : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  rw [old_def, case_def, bind_assoc_capture J central]
  congr 1
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · have unpack : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← route_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have projection :
        ((E ◁ (coprod.inl : A ⟶ A ⨿ B)) ▷ X) ≫ (fst E (A ⨿ B) ▷ X) =
          fst E A ▷ X := by
      rw [← MonoidalCategory.comp_whiskerRight, CartesianMonoidalCategory.whiskerLeft_fst]
    rw [← Category.assoc, unpack, ← bind_pre_map, reassoc_of% route_left, coprod.inl_desc,
      ← J.map_comp_assoc, projection]
    change _ = coprod.inl ≫ inv route ≫ route ≫ _
    rw [IsIso.inv_hom_id_assoc, coprod.inl_desc]
  · have unpack : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← route_right, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have projection :
        ((E ◁ (coprod.inr : B ⟶ A ⨿ B)) ▷ X) ≫ (fst E (A ⨿ B) ▷ X) =
          fst E B ▷ X := by
      rw [← MonoidalCategory.comp_whiskerRight, CartesianMonoidalCategory.whiskerLeft_fst]
    rw [← Category.assoc, unpack, ← bind_pre_map, reassoc_of% route_right, coprod.inr_desc,
      ← J.map_comp_assoc, projection]
    change _ = coprod.inr ≫ inv route ≫ route ≫ _
    rw [IsIso.inv_hom_id_assoc, coprod.inr_desc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
