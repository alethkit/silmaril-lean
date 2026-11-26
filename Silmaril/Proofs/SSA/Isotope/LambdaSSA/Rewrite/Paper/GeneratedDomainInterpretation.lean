module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Domain.Interpretation.Defs

/-! # Uniqueness for interpretations defined on generated arrows -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GeneratedDomainInterpretation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton.Generation (Coordinates Generated)
open Paper.Extension.Singleton.Generation.Domain

universe u v w x

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {C : Type w} [CategoryTheory.Category.{x} C] [PremonoidalCategory C]
  [HasFiniteCoproducts C] [Iteration C] {X : τ → C} {T : Coordinates X}
  {instruction : ∀ p : Φ, X (instrSrc p) ⟶ X (instrTrg p)}

local notation "Obj" => ofType (Seed)

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
private theorem map_id {F : Paper.Extension.Singleton.Generation.Domain.Category Seed ⥤ C}
    (o : ∀ A, F.obj (Obj A) ≅ X A) (A : τ) :
    mapInCoordinates Seed F o (𝟙 (Obj A)) = 𝟙 (X A) := by
  simp [mapInCoordinates]

omit [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
private theorem map_comp {F : Paper.Extension.Singleton.Generation.Domain.Category Seed ⥤ C}
    (o : ∀ A, F.obj (Obj A) ≅ X A) {A B D : τ} (f : Obj A ⟶ Obj B) (g : Obj B ⟶ Obj D) :
    mapInCoordinates Seed F o (f ≫ g) = mapInCoordinates Seed F o f ≫ mapInCoordinates Seed F o g := by
  simp [mapInCoordinates]

omit [CategoryTheory.Category.{x} C] [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
private theorem inl_copair {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    inl Seed A B ≫ copair Seed f g = f :=
  WideSubcategory.hom_ext _ ((Paper.Extension.Singleton.sumCofanIsColimit Seed A B).fac
    (BinaryCofan.mk f.hom g.hom) ⟨WalkingPair.left⟩)

omit [CategoryTheory.Category.{x} C] [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C] in
private theorem inr_copair {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    inr Seed A B ≫ copair Seed f g = g :=
  WideSubcategory.hom_ext _ ((Paper.Extension.Singleton.sumCofanIsColimit Seed A B).fac
    (BinaryCofan.mk f.hom g.hom) ⟨WalkingPair.right⟩)

variable (I K : Interpretation Seed T instruction)

local notation "mapI" => mapInCoordinates (Seed) (Interpretation.functor I) (Interpretation.objIso I)
local notation "mapK" => mapInCoordinates (Seed) (Interpretation.functor K) (Interpretation.objIso K)

set_option backward.isDefEq.respectTransparency false in
private theorem map_copair {A B D : τ} (f : Obj A ⟶ Obj D) (g : Obj B ⟶ Obj D) :
    mapI (copair Seed f g) = (T.sumIso A B).hom ≫
      coprod.desc (mapI f) (mapI g) := by
  apply (cancel_epi (T.sumIso A B).inv).mp
  apply coprod.hom_ext
  · rw [← Category.assoc, ← I.inl, ← map_comp, inl_copair]
    simp only [Iso.inv_hom_id_assoc, coprod.inl_desc]
  · rw [← Category.assoc, ← I.inr, ← map_comp, inr_copair]
    simp only [Iso.inv_hom_id_assoc, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
private theorem map_inv_eq {A B : τ} (i : Obj A ≅ Obj B) (h : mapI i.hom = mapK i.hom) :
    mapI i.inv = mapK i.inv := by
  have : IsIso (mapK i.hom) := by
    unfold mapInCoordinates
    infer_instance
  apply (cancel_mono (mapK i.hom)).mp
  calc
    _ = mapI (i.inv ≫ i.hom) := by rw [map_comp, h]
    _ = mapK (i.inv ≫ i.hom) := by simp only [Iso.inv_hom_id, map_id]
    _ = _ := by rw [map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem map_eq_of_generated {A B : τ}
    {f : Paper.Extension.Singleton.ofType Seed A ⟶ Paper.Extension.Singleton.ofType Seed B}
    (hf : Generated Seed (A := A) (B := B) f) :
    mapI (ofGenerated Seed hf) = mapK (ofGenerated Seed hf) := by
  induction hf with
  | id A => exact (map_id Seed I.objIso A).trans (map_id Seed K.objIso A).symm
  | comp hf hg ihf ihg =>
    change mapI (ofGenerated Seed hf ≫ ofGenerated Seed hg) = mapK (ofGenerated Seed hf ≫ ofGenerated Seed hg)
    rw [map_comp, map_comp, ihf, ihg]
  | inv i hi ih =>
    let g : _ ≅ _ :=
      { hom := ofGenerated Seed hi
        inv := ofGenerated Seed (.inv i hi)
        hom_inv_id := WideSubcategory.hom_ext _ i.hom_inv_id
        inv_hom_id := WideSubcategory.hom_ext _ i.inv_hom_id }
    exact map_inv_eq Seed I K g ih
  | discard A => exact (I.discard A).trans (K.discard A).symm
  | fst A B => exact (I.fst A B).trans (K.fst A B).symm
  | snd A B => exact (I.snd A B).trans (K.snd A B).symm
  | copy A => exact (I.copy A).trans (K.copy A).symm
  | primitive p => exact (I.primitive p).trans (K.primitive p).symm
  | initial => exact T.initial.hom_ext _ _
  | inl A B => exact (I.inl A B).trans (K.inl A B).symm
  | inr A B => exact (I.inr A B).trans (K.inr A B).symm
  | copair hf hg ihf ihg =>
    change mapI (copair Seed (ofGenerated Seed hf) (ofGenerated Seed hg)) =
      mapK (copair Seed (ofGenerated Seed hf) (ofGenerated Seed hg))
    rw [map_copair, map_copair, ihf, ihg]
  | left Y hf ih =>
    change mapI (whiskerLeft Seed Y (ofGenerated Seed hf)) =
      mapK (whiskerLeft Seed Y (ofGenerated Seed hf))
    rw [I.left, K.left, ih]
  | right Y hf ih =>
    change mapI (whiskerRight Seed Y (ofGenerated Seed hf)) =
      mapK (whiskerRight Seed Y (ofGenerated Seed hf))
    rw [I.right, K.right, ih]
  | iterate hf ih =>
    change mapI (iterateSum Seed (ofGenerated Seed hf)) =
      mapK (iterateSum Seed (ofGenerated Seed hf))
    rw [I.iterate, K.iterate, ih]

theorem map_eq {A B : τ} (f : Obj A ⟶ Obj B) : mapI f = mapK f :=
  map_eq_of_generated Seed I K (A := A) (B := B) f.property

set_option backward.isDefEq.respectTransparency false in
private theorem naturality {A B : τ} (f : Obj A ⟶ Obj B) :
    I.functor.map f ≫ (I.objIso B ≪≫ (K.objIso B).symm).hom =
      (I.objIso A ≪≫ (K.objIso A).symm).hom ≫ K.functor.map f := by
  have h := congrArg (fun k => (I.objIso A).hom ≫ k ≫ (K.objIso B).inv) (map_eq Seed I K f)
  simpa only [mapInCoordinates, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.trans_hom, Iso.symm_hom] using h

set_option backward.isDefEq.respectTransparency false in
theorem comparison_existsUnique :
    ∃! e : I.functor ≅ K.functor, ∀ A : τ,
      e.hom.app (Obj A) = (I.objIso A ≪≫ (K.objIso A).symm).hom := by
  let e : I.functor ≅ K.functor := NatIso.ofComponents
    (fun A => I.objIso (show τ from A.obj.as) ≪≫ (K.objIso (show τ from A.obj.as)).symm)
    (fun {A B} f => naturality Seed I K (A := (show τ from A.obj.as)) (B := (show τ from B.obj.as)) f)
  refine ⟨e, fun _ => rfl, ?_⟩
  intro other h
  apply Iso.ext
  ext A
  exact h (show τ from A.obj.as)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GeneratedDomainInterpretation
