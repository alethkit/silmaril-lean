module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationBind
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality

/-! # Postcomposition of a contextual dispatcher on outward exits -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate extend retainLeft splitMapCoprod)

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
  (J : V ⥤ C)

section Distributive

variable [DistributiveFreydCategory J]

noncomputable def retainEnvironment {E X Y : V} (p : X ⟶ E) (f : J.obj X ⟶ J.obj Y) :
    J.obj X ⟶ J.obj (E ⊗ Y) :=
  J.map (lift p (𝟙 X)) ≫ retainLeft J f

@[expose] noncomputable def routeEnvironment (E A B : V) :
    J.obj (E ⊗ (A ⨿ B)) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ B) :=
  J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)

theorem retainEnvironment_comp {E X Y Z : V} (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) (g : J.obj Y ⟶ J.obj Z) :
    retainEnvironment J p (f ≫ g) = retainEnvironment J p f ≫ retainLeft J g := by
  simp only [retainEnvironment, retainLeft_comp, Category.assoc]

theorem retainEnvironment_map {E X Y : V} (p : X ⟶ E) (f : X ⟶ Y) :
    retainEnvironment J p (J.map f) = J.map (lift p f) := by
  rw [retainEnvironment, retainLeft_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc] theorem retainEnvironment_pre {E X Y D : V} (q : D ⟶ X) (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) :
    J.map q ≫ retainEnvironment J p f = retainEnvironment J (q ≫ p) (J.map q ≫ f) := by
  rw [retainEnvironment_comp, retainEnvironment_map, retainEnvironment, ← J.map_comp_assoc]
  congr 2
  simp

@[reassoc] theorem retainEnvironment_snd [FreydCategory.CentralUnit J]
    {E X Y : V} (p : X ⟶ E) (f : J.obj X ⟶ J.obj Y) :
    retainEnvironment J p f ≫ J.map (snd E Y) = f := by
  simp only [retainEnvironment, retainLeft, leftTensor, id_whiskerRight,
    Category.id_comp, Category.assoc, FreydCategory.whiskerLeft_snd]
  rw [← J.map_comp_assoc, CartesianMonoidalCategory.lift_snd, J.map_id, Category.id_comp]

@[reassoc] theorem retainEnvironment_twice {E X Y : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (p : X ⟶ E) (f : J.obj X ⟶ J.obj Y) :
    retainEnvironment J p (retainEnvironment J p f) =
      retainEnvironment J p f ≫ J.map (lift (fst E Y) (𝟙 (E ⊗ Y))) := by
  have copy :
      lift p (𝟙 X) ≫ E ◁ lift p (𝟙 X) =
      lift p (𝟙 X) ≫ lift (fst E X) (𝟙 (E ⊗ X)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  simp only [retainEnvironment, retainLeft_comp, retainLeft_map, Category.assoc]
  rw [← J.map_comp_assoc, copy, J.map_comp_assoc, ← copyValue, retainLeft_copy J f central, copyValue]

@[expose] noncomputable def liftExit {E A B D : V}
    (k : J.obj (E ⊗ A) ⟶ J.obj D) :
    J.obj (E ⊗ (A ⨿ B)) ⟶ J.obj (D ⨿ B) :=
  routeEnvironment J E A B ≫
    coprod.desc (k ≫ J.map (coprod.inl : D ⟶ D ⨿ B)) (J.map (snd E B ≫ coprod.inr))

private theorem capture_liftExit {E A B D : V}
    (k : J.obj (E ⊗ A) ⟶ J.obj D) :
    retainEnvironment J (fst E (A ⨿ B)) (liftExit J k) ≫ routeEnvironment J E D B =
      routeEnvironment J E A B ≫
        coprod.map (retainEnvironment J (fst E A) k) (𝟙 (J.obj (E ⊗ B))) := by
  let route := routeEnvironment J E A B
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have hr : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  have hli : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
    rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hri : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have outL :
      J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ liftExit J (B := B) k =
        k ≫ J.map (coprod.inl : D ⟶ D ⨿ B) := by
    rw [liftExit, reassoc_of% hl, coprod.inl_desc]
  have outR :
      J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ liftExit J (B := B) k =
        J.map (snd E B ≫ (coprod.inr : B ⟶ D ⨿ B)) := by
    rw [liftExit, reassoc_of% hr, coprod.inr_desc]
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · simp only [reassoc_of% hli]
    rw [retainEnvironment_pre_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      outL, retainEnvironment_comp, retainLeft_map]
    rw [reassoc_of% hl, coprod.inl_map]
    simp only [Category.assoc, routeEnvironment]
    exact congrArg (retainEnvironment J (fst E A) k ≫ ·) (distributeMap_inl J E D B)
  · simp only [reassoc_of% hri]
    rw [retainEnvironment_pre_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      outR, retainEnvironment_map]
    have prodMap :
        lift (fst E B) (snd E B ≫ (coprod.inr : B ⟶ D ⨿ B)) = E ◁ coprod.inr := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [prodMap]
    rw [reassoc_of% hr, coprod.inr_map, Category.id_comp]
    exact distributeMap_inr J E D B

private theorem route_tensor_comparison (E A B : V) :
    routeEnvironment J E A B =
      (Functor.StrongPremonoidal.tensorIso (J := J) E (A ⨿ B)).inv ≫
        (J.obj E ◁ splitMapCoprod J A B) ≫
        DistributivePremonoidalCategory.leftInv (J.obj E) (J.obj A) (J.obj B) ≫
        coprod.map (Functor.StrongPremonoidal.tensorIso (J := J) E A).hom
          (Functor.StrongPremonoidal.tensorIso (J := J) E B).hom := by
  let t := Functor.StrongPremonoidal.tensorIso (J := J)
  let route := routeEnvironment J E A B
  let δ := DistributiveTensor.leftIso (J.obj E) (J.obj A) (J.obj B)
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have ht {P Q : V} (f : P ⟶ Q) :
      J.map (E ◁ f) ≫ (t E Q).inv = (t E P).inv ≫ J.obj E ◁ J.map f := by
    apply (cancel_mono (t E Q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Functor.StrongPremonoidal.tensor_naturality_right, Iso.inv_hom_id_assoc]
  have hl : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have hr : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  have δl : (J.obj E ◁ (coprod.inl : J.obj A ⟶ J.obj A ⨿ J.obj B)) ≫ δ.inv = coprod.inl := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  have δr : (J.obj E ◁ (coprod.inr : J.obj B ⟶ J.obj A ⨿ J.obj B)) ≫ δ.inv = coprod.inr := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · have hinv : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, hl, reassoc_of% hinv, reassoc_of% (ht (coprod.inl : A ⟶ A ⨿ B)),
      ← whiskerLeft_comp_assoc]
    have hc : J.map (coprod.inl : A ⟶ A ⨿ B) ≫ splitMapCoprod J A B = coprod.inl :=
      map_inl_inv_coprodComparison J
    rw [hc]
    change _ = (t E A).inv ≫ (J.obj E ◁ coprod.inl) ≫ δ.inv ≫ _
    rw [reassoc_of% δl, coprod.inl_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · have hinv : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, hr, reassoc_of% hinv, reassoc_of% (ht (coprod.inr : B ⟶ A ⨿ B)),
      ← whiskerLeft_comp_assoc]
    have hc : J.map (coprod.inr : B ⟶ A ⨿ B) ≫ splitMapCoprod J A B = coprod.inr :=
      map_inr_inv_coprodComparison J
    rw [hc]
    change _ = (t E B).inv ≫ (J.obj E ◁ coprod.inr) ≫ δ.inv ≫ _
    rw [reassoc_of% δr, coprod.inr_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem route_graph (E A B : V) :
    retainEnvironment J (fst E (A ⨿ B)) (J.map (DistributiveTensor.leftIso E A B).inv) ≫
        routeEnvironment J E (E ⊗ A) (E ⊗ B) =
      routeEnvironment J E A B ≫ Limits.coprod.map
        (J.map (lift (fst E A) (𝟙 (E ⊗ A)))) (J.map (lift (fst E B) (𝟙 (E ⊗ B)))) := by
  let δ := DistributiveTensor.leftIso E A B
  let route := routeEnvironment J E A B
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
    distributeMap_inl J E A B
  have hr : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
    distributeMap_inr J E A B
  have δl : (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ δ.inv = coprod.inl := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  have δr : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ δ.inv = coprod.inr := by
    apply (cancel_mono δ.hom).mp
    simp [δ, DistributiveTensor.leftIso]
  apply (cancel_epi (inv route)).mp
  apply coprod.hom_ext
  · have hinv : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← hl, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, retainEnvironment_pre_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      ← J.map_comp, δl, retainEnvironment_map]
    have graph : lift (fst E A) (coprod.inl : E ⊗ A ⟶ (E ⊗ A) ⨿ (E ⊗ B)) =
        lift (fst E A) (𝟙 _) ≫ (E ◁ coprod.inl) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [graph, J.map_comp_assoc, reassoc_of% hinv, reassoc_of% hl, coprod.inl_map]
    simpa only [routeEnvironment, Category.assoc] using
      congrArg (J.map (lift (fst E A) (𝟙 (E ⊗ A))) ≫ ·)
        (distributeMap_inl J E (E ⊗ A) (E ⊗ B))
  · have hinv : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← hr, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hinv, retainEnvironment_pre_assoc, CartesianMonoidalCategory.whiskerLeft_fst,
      ← J.map_comp, δr, retainEnvironment_map]
    have graph : lift (fst E B) (coprod.inr : E ⊗ B ⟶ (E ⊗ A) ⨿ (E ⊗ B)) =
        lift (fst E B) (𝟙 _) ≫ (E ◁ coprod.inr) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [graph, J.map_comp_assoc, reassoc_of% hinv, reassoc_of% hr, coprod.inr_map]
    simpa only [routeEnvironment, Category.assoc] using
      congrArg (J.map (lift (fst E B) (𝟙 (E ⊗ B))) ≫ ·)
        (distributeMap_inr J E (E ⊗ A) (E ⊗ B))

theorem bind_retainEnvironment {E X Y D : V} (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) (k : J.obj (E ⊗ Y) ⟶ J.obj D) :
    bindArrow J f (J.map (p ▷ Y) ≫ k) = retainEnvironment J p f ≫ k := by
  have h : duplicate X ≫ p ▷ X = lift p (𝟙 X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        duplicate, CartesianMonoidalCategory.lift_fst_assoc, Category.id_comp,
        CartesianMonoidalCategory.lift_fst]
    · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        duplicate, CartesianMonoidalCategory.lift_snd]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_eq_retainLeft, retainEnvironment, Category.assoc]
  rw [← retainLeft_pre_assoc, ← J.map_comp_assoc, h]

theorem caseWithContext_liftExit [FreydCategory.CentralUnit J] {E A B D Z : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (f : J.obj E ⟶ J.obj (A ⨿ B)) (k : J.obj (E ⊗ A) ⟶ J.obj D)
    (out : J.obj D ⟶ J.obj Z) (loop : J.obj (E ⊗ B) ⟶ J.obj Z) :
    caseWithContext J (bindArrow J f (liftExit J k)) (J.map (snd E D) ≫ out) loop =
      caseWithContext J f (k ≫ out) loop := by
  change bindArrow J (bindArrow J f (liftExit J k))
    (J.map (DistributiveTensor.leftIso E D B).inv ≫ splitMapCoprod J (E ⊗ D) (E ⊗ B) ≫ _) =
    bindArrow J f
      (J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) ≫ _)
  rw [bind_assoc_capture J central, bind_retainEnvironment]
  have h := capture_liftExit J (B := B) k
  change retainEnvironment J (fst E (A ⨿ B)) (liftExit J k) ≫
      routeEnvironment J E D B = _ at h
  have assoc := reassoc_of% h
  change bindArrow J f (retainEnvironment J (fst E (A ⨿ B)) (liftExit J k) ≫
    (J.map (DistributiveTensor.leftIso E D B).inv ≫ splitMapCoprod J (E ⊗ D) (E ⊗ B) ≫ _)) = _
  have route (E A B : V) : routeEnvironment J E A B =
      J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) := rfl
  simp only [route, Category.assoc] at assoc
  rw [assoc, Limits.coprod.map_desc, Category.id_comp, retainEnvironment_snd_assoc]

theorem bind_purePayload {E B D : V} (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (J.map (snd E B)) (J.map (fst E B ▷ B) ≫ k) = k := by
  have h : lift (fst E B) (snd E B) = 𝟙 (E ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [bind_retainEnvironment, retainEnvironment_map, h, J.map_id, Category.id_comp]

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- The ordinary iteration body of a contextual loop, keeping the environment
in either the exit or recursion summand. -/
noncomputable def contextualStep {E A B : V}
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    J.obj (E ⊗ A) ⟶ J.obj (E ⊗ B) ⨿ J.obj (E ⊗ A) :=
  retainEnvironment J (fst E A) body ≫ routeEnvironment J E B A

theorem contextualStep_liftExit {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    contextualStep J (retainEnvironment J (fst E A) body ≫ liftExit J k) =
      contextualStep J body ≫ Limits.coprod.map (retainEnvironment J (fst E B) k) (𝟙 _) := by
  simp only [contextualStep, retainEnvironment_comp, retainEnvironment_twice J central,
    Category.assoc]
  simpa only [retainEnvironment, Category.assoc] using
    congrArg (retainEnvironment J (fst E A) body ≫ ·) (capture_liftExit J (B := A) k)

theorem contextualLoop_eq_step {E A B : V} (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J body = iterate (contextualStep J body) ≫ J.map (snd E B) := by
  simp only [contextualLoop, contextualStep, retainEnvironment, routeEnvironment, Category.assoc]

theorem contextualLoop_liftExit [FreydCategory.CentralUnit J] {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k) =
      iterate (contextualStep J body) ≫ k := by
  rw [contextualLoop_eq_step, contextualStep_liftExit J central, ← ElgotCategory.naturality, Category.assoc, retainEnvironment_snd]

omit [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [DistributivePremonoidalCategory C] in
private theorem iterate_retype {X X' Y Y' : C} (e : X = X') (k : Y ⟶ Y')
    (f : X ⟶ Y ⨿ X) :
    iterate ((eqToIso e).inv ≫ f ≫ Limits.coprod.map k (eqToIso e).hom) =
      (eqToIso e).inv ≫ iterate f ≫ k := by
  subst X'
  simpa using (ElgotCategory.naturality f k).symm

theorem retainLeft_iterate_shared {E X Y : V}
    (shared : ∃ e : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso e)
    (body : J.obj X ⟶ J.obj (Y ⨿ X)) :
    iterate (retainLeft J (R := E) body ≫ routeEnvironment J E Y X) =
      retainLeft J (R := E) (iterate (body ≫ splitMapCoprod J Y X)) := by
  let t := Functor.StrongPremonoidal.tensorIso (J := J)
  let f := body ≫ splitMapCoprod J Y X
  let δ := DistributivePremonoidalCategory.leftInv (J.obj E) (J.obj Y) (J.obj X)
  let g := (J.obj E ◁ f) ≫ δ
  have step : retainLeft J (R := E) body ≫ routeEnvironment J E Y X =
      (t E X).inv ≫ g ≫ Limits.coprod.map (t E Y).hom (t E X).hom := by
    rw [route_tensor_comparison]
    simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_assoc, g, f, t, δ, whiskerLeft_comp]
  have reindex :
      iterate ((t E X).inv ≫ g ≫ Limits.coprod.map (t E Y).hom (t E X).hom) =
        (t E X).inv ≫ iterate g ≫ (t E Y).hom := by
    obtain ⟨h, ht⟩ := shared
    change t E X = eqToIso h at ht
    rw [ht]
    exact iterate_retype h (t E Y).hom g
  rw [step, reindex]
  dsimp only [g, δ]
  rw [StrongElgotFreydCategory.strength J]
  simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp, f, t]

theorem contextualLoop_retain {E A B : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (shared : ∃ e : J.obj E ⊗ J.obj (E ⊗ A) = J.obj (E ⊗ (E ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) E (E ⊗ A) = eqToIso e)
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    retainEnvironment J (fst E A) (contextualLoop J body) = iterate (contextualStep J body) := by
  let X := E ⊗ A
  let Y := E ⊗ B
  let f := retainEnvironment J (fst E A) body ≫ J.map (DistributiveTensor.leftIso E B A).inv
  let g := retainLeft J (R := E) f ≫ routeEnvironment J E Y X
  let graph (T : V) := lift (fst E T) (𝟙 (E ⊗ T))
  have old : f ≫ splitMapCoprod J Y X = contextualStep J body := by
    simp only [f, X, Y, contextualStep, routeEnvironment, Category.assoc]
  have simulation : contextualStep J body ≫ Limits.coprod.map (J.map (graph B)) (J.map (graph A)) =
      J.map (graph A) ≫ g := by
    have eq : retainEnvironment J (fst E A) f =
        retainEnvironment J (fst E A) body ≫
          retainEnvironment J (fst E (B ⨿ A)) (J.map (DistributiveTensor.leftIso E B A).inv) := by
      dsimp only [f]
      rw [retainEnvironment_comp, retainEnvironment_twice J central]
      simp only [retainEnvironment, Category.assoc]
    calc
      _ = retainEnvironment J (fst E A) f ≫ routeEnvironment J E Y X := by
        simp only [graph, X, Y, contextualStep, Category.assoc, ← route_graph J E B A, eq]
      _ = _ := by simp only [retainEnvironment, graph, g, Category.assoc]
  have transport : iterate (contextualStep J body) ≫ J.map (graph B) = J.map (graph A) ≫ iterate g := by
    rw [ElgotCategory.naturality]
    apply ElgotFreydCategory.uniformity (J := J)
    rw [Category.assoc]
    have maps : Limits.coprod.map (J.map (graph B)) (𝟙 _) ≫ Limits.coprod.map (𝟙 _) (J.map (graph A)) =
        Limits.coprod.map (J.map (graph B)) (J.map (graph A)) := by
      apply Limits.coprod.hom_ext <;> simp
    rw [maps, simulation]
  have finish : graph B ≫ (E ◁ snd E B) = 𝟙 (E ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [graph]
  rw [contextualLoop_eq_step, retainEnvironment_comp, retainLeft_map]
  change (J.map (graph A) ≫ retainLeft J (iterate (contextualStep J body))) ≫ J.map (E ◁ snd E B) = _
  rw [← old, ← retainLeft_iterate_shared J shared, ← show g =
    retainLeft J (R := E) f ≫ routeEnvironment J E Y X from rfl, ← transport,
    Category.assoc, ← J.map_comp, finish, J.map_id, Category.comp_id, old]

theorem caseLoop_exitContinuation [FreydCategory.CentralUnit J] {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (shared : ∃ e : J.obj E ⊗ J.obj (E ⊗ A) = J.obj (E ⊗ (E ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) E (E ⊗ A) = eqToIso e)
    (entry : J.obj E ⟶ J.obj (B ⨿ A))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (bindArrow J entry (liftExit J k)) (J.map (snd E D))
        (contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k)) =
      bindArrow J (caseWithContext J entry (J.map (snd E B)) (contextualLoop J body)) k := by
  have h := caseWithContext_liftExit J central entry k (𝟙 (J.obj D))
    (contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k))
  simp only [Category.comp_id] at h
  rw [h, contextualLoop_liftExit J central, bind_case_capture J central, bind_purePayload,
    bind_retainEnvironment, contextualLoop_retain J central shared]

end Iteration

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
