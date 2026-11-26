module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Project the ordinary Paper iteration equations through the chosen coproducts -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedElgot

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "proj" => projection Seed
local notation "c" => PreservesColimitPair.iso (proj)

private theorem c_desc {X Y Z : P} (f : X ⟶ Z) (g : Y ⟶ Z) :
    coprod.desc ((proj).map f) ((proj).map g) = (c X Y).hom ≫ (proj).map (coprod.desc f g) := by
  apply coprod.hom_ext <;>
    simp only [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, inr_coprodComparison_assoc,
      coprod.inl_desc, coprod.inr_desc, ← Functor.map_comp]

private theorem c_map {X Y X' Y' : P} (f : X ⟶ X') (g : Y ⟶ Y') :
    coprod.map ((proj).map f) ((proj).map g) ≫ (c X' Y').hom =
      (c X Y).hom ≫ (proj).map (coprod.map f g) := by
  apply coprod.hom_ext <;>
    simp only [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, inr_coprodComparison_assoc,
      coprod.inl_map_assoc, coprod.inr_map_assoc, inl_coprodComparison, inr_coprodComparison,
      ← Functor.map_comp, coprod.inl_map, coprod.inr_map]

set_option backward.isDefEq.respectTransparency false in
private theorem sumIso_map (A B : τ) :
    (proj).mapIso (Paper.TypeCategory.sumIso A B) =
      sumIso Seed A B ≪≫ c (Paper.TypeCategory.ofType A) (Paper.TypeCategory.ofType B) := by
  apply Iso.ext
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed A B)
  · change (proj).map (Paper.TypeCategory.sumCofan A B).inl ≫ (proj).map (Paper.TypeCategory.sumIso A B).hom =
      (sumCofan Seed A B).inl ≫ (sumIso Seed A B).hom ≫ (c _ _).hom
    rw [← Functor.map_comp, Paper.TypeCategory.sumCofan_inl_sumIso_hom,
      ← Category.assoc (sumCofan Seed A B).inl, sumCofan_inl_sumIso_hom,
      PreservesColimitPair.iso_hom, inl_coprodComparison]
  · change (proj).map (Paper.TypeCategory.sumCofan A B).inr ≫ (proj).map (Paper.TypeCategory.sumIso A B).hom =
      (sumCofan Seed A B).inr ≫ (sumIso Seed A B).hom ≫ (c _ _).hom
    rw [← Functor.map_comp, Paper.TypeCategory.sumCofan_inr_sumIso_hom,
      ← Category.assoc (sumCofan Seed A B).inr, sumCofan_inr_sumIso_hom,
      PreservesColimitPair.iso_hom, inr_coprodComparison]

set_option backward.isDefEq.respectTransparency false in
theorem iterateChosen_projectStep {X Y : P} (f : X ⟶ Y ⨿ X) :
    iterateChosen Seed (projectStep Seed f) = (proj).map (Paper.TypeCategory.iterate f) := by
  have e : (c Y X).inv ≫ (sumIso Seed ((proj).obj Y).as ((proj).obj X).as).inv =
      (proj).map (Paper.TypeCategory.sumIso (show τ from Y) (show τ from X)).inv :=
    (congrArg Iso.inv (sumIso_map Seed (show τ from Y) (show τ from X))).symm
  unfold iterateChosen Paper.TypeCategory.iterate
  rw [Category.assoc, e, ← Functor.map_comp, iterateSum_map]

private theorem exists_projectStep {X Y : Q} (f : X ⟶ Y ⨿ X) :
    ∃ f₀ : X.as ⟶ Y.as ⨿ X.as, projectStep Seed f₀ = f := by
  obtain ⟨f₀, hf⟩ := (proj).map_surjective (f ≫ (c Y.as X.as).hom)
  exact ⟨f₀, by rw [show projectStep Seed f₀ = (proj).map f₀ ≫ (c Y.as X.as).inv from rfl,
    hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

set_option backward.isDefEq.respectTransparency false in
theorem iterateChosen_fixpoint {X Y : Q} (f : X ⟶ Y ⨿ X) :
    iterateChosen Seed f = f ≫ coprod.desc (𝟙 Y) (iterateChosen Seed f) := by
  obtain ⟨f₀, rfl⟩ := exists_projectStep Seed f
  rw [iterateChosen_projectStep Seed]
  calc
    _ = (proj).map f₀ ≫ (proj).map (coprod.desc (𝟙 Y.as) (Paper.TypeCategory.iterate f₀)) := by
      rw [← Functor.map_comp]
      exact congrArg (proj).map (Paper.TypeCategory.iterate_fixpoint f₀)
    _ = _ := by
      change _ = ((proj).map f₀ ≫ (c Y.as X.as).inv) ≫
        coprod.desc (𝟙 Y) ((proj).map (Paper.TypeCategory.iterate f₀))
      rw [← (show (proj).map (𝟙 Y.as) = 𝟙 Y from (proj).map_id Y.as), c_desc, Category.assoc, Iso.inv_hom_id_assoc]

private theorem c_inv_map {X Y X' Y' : P} (f : X ⟶ X') (g : Y ⟶ Y') :
    (c X Y).inv ≫ coprod.map ((proj).map f) ((proj).map g) =
      (proj).map (coprod.map f g) ≫ (c X' Y').inv := by
  apply (cancel_mono (c X' Y').hom).1
  rw [Category.assoc, Category.assoc, c_map, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem iterateChosen_naturality {X Y Z : Q} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterateChosen Seed f ≫ g = iterateChosen Seed (f ≫ coprod.map g (𝟙 X)) := by
  obtain ⟨f₀, rfl⟩ := exists_projectStep Seed f
  obtain ⟨g₀, rfl⟩ := (proj).map_surjective (X := Y.as) (Y := Z.as) g
  have step : projectStep Seed f₀ ≫ coprod.map ((proj).map g₀) (𝟙 X) =
      projectStep Seed (f₀ ≫ coprod.map g₀ (𝟙 X.as)) := by
    change ((proj).map f₀ ≫ (c Y.as X.as).inv) ≫ coprod.map ((proj).map g₀) (𝟙 X) =
      (proj).map (f₀ ≫ coprod.map g₀ (𝟙 X.as)) ≫ (c Z.as X.as).inv
    rw [Functor.map_comp, Category.assoc, ← (show (proj).map (𝟙 X.as) = 𝟙 X from (proj).map_id X.as), c_inv_map, Category.assoc]
  rw [step, iterateChosen_projectStep Seed, iterateChosen_projectStep Seed, ← Functor.map_comp, Paper.TypeCategory.iterate_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem project_flatten {X Y : P} :
    (c (Y ⨿ X) X).inv ≫ coprod.map (c Y X).inv (𝟙 ((proj).obj X)) ≫
        coprod.desc (𝟙 ((proj).obj Y ⨿ (proj).obj X)) coprod.inr =
      (proj).map (coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) ≫ (c Y X).inv := by
  apply (cancel_epi (c (Y ⨿ X) X).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc]
  apply (cancel_mono (c Y X).hom).1
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ← c_desc, (proj).map_id (Y ⨿ X)]
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, Category.id_comp, Iso.inv_hom_id]
  · simp only [coprod.inr_map_assoc, coprod.inr_desc_assoc, coprod.inr_desc, Category.id_comp,
      PreservesColimitPair.iso_hom, inr_coprodComparison]

set_option backward.isDefEq.respectTransparency false in
theorem iterateChosen_codiagonal {X Y : Q} (f : X ⟶ (Y ⨿ X) ⨿ X) :
    iterateChosen Seed (iterateChosen Seed f) =
      iterateChosen Seed (f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) := by
  let u := coprod.mapIso (c Y.as X.as) (Iso.refl X)
  obtain ⟨f₀, hf₀⟩ := exists_projectStep Seed (f ≫ u.hom)
  have hf : f = projectStep Seed f₀ ≫ coprod.map (c Y.as X.as).inv (𝟙 X) := by
    change f = projectStep Seed f₀ ≫ u.inv
    rw [hf₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have flat : f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X) =
      projectStep Seed (f₀ ≫ coprod.desc (𝟙 (Y.as ⨿ X.as)) coprod.inr) := by
    rw [hf]
    change (((proj).map f₀ ≫ (c (Y.as ⨿ X.as) X.as).inv) ≫ coprod.map (c Y.as X.as).inv (𝟙 X)) ≫
      coprod.desc (𝟙 (Y ⨿ X)) coprod.inr = (proj).map (f₀ ≫ coprod.desc (𝟙 (Y.as ⨿ X.as)) coprod.inr) ≫
        (c Y.as X.as).inv
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (fun k => (proj).map f₀ ≫ k) (project_flatten Seed (X := X.as) (Y := Y.as))
  have nested : iterateChosen Seed f = projectStep Seed (Paper.TypeCategory.iterate f₀) := by
    rw [hf, ← iterateChosen_naturality, iterateChosen_projectStep]
  rw [flat, nested, iterateChosen_projectStep Seed, iterateChosen_projectStep Seed, Paper.TypeCategory.iterate_codiagonal]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem iterateChosen_roll {X Y Z : Q} (h : X ⟶ Z) (s : Z ⟶ Y ⨿ X) :
    iterateChosen Seed (h ≫ s) =
      h ≫ iterateChosen Seed (s ≫ coprod.map (𝟙 Y) h) := by
  obtain ⟨h₀, rfl⟩ := (proj).map_surjective (X := X.as) (Y := Z.as) h
  let s₁ := s ≫ (c Y.as X.as).hom
  obtain ⟨s₀, hs₀⟩ := (proj).map_surjective (X := Z.as) (Y := Y.as ⨿ X.as) s₁
  have hs : s = (proj).map s₀ ≫ (c Y.as X.as).inv := by
    rw [hs₀]
    change s = (s ≫ (c Y.as X.as).hom) ≫ (c Y.as X.as).inv
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have l : (proj).map h₀ ≫ s = projectStep Seed (h₀ ≫ s₀) := by
    rw [hs]
    change (proj).map h₀ ≫ (proj).map s₀ ≫ (c Y.as X.as).inv =
      (proj).map (h₀ ≫ s₀) ≫ (c Y.as X.as).inv
    rw [Functor.map_comp, Category.assoc]
  have r : s ≫ coprod.map (𝟙 Y) ((proj).map h₀) =
      projectStep Seed (s₀ ≫ coprod.map (𝟙 Y.as) h₀) := by
    rw [hs]
    change ((proj).map s₀ ≫ (c Y.as X.as).inv) ≫ coprod.map (𝟙 Y) ((proj).map h₀) =
      (proj).map (s₀ ≫ coprod.map (𝟙 Y.as) h₀) ≫ (c Y.as Z.as).inv
    rw [Functor.map_comp, Category.assoc, ← (show (proj).map (𝟙 Y.as) = 𝟙 Y from (proj).map_id Y.as), c_inv_map, Category.assoc]
  rw [l, r, iterateChosen_projectStep Seed, iterateChosen_projectStep Seed,
    ← Functor.map_comp, Paper.TypeCategory.iterate_roll]

set_option backward.isDefEq.respectTransparency false in
theorem projectSquare_iff {X Y Z : P} (f : X ⟶ Y ⨿ X) (g : Z ⟶ Y ⨿ Z) (h : X ⟶ Z) :
    projectStep Seed f ≫ coprod.map (𝟙 ((proj).obj Y)) ((proj).map h) = (proj).map h ≫ projectStep Seed g ↔
    (proj).map (f ≫ coprod.map (𝟙 Y) h) = (proj).map (h ≫ g) := by
  change ((proj).map f ≫ (c Y X).inv) ≫ coprod.map (𝟙 ((proj).obj Y)) ((proj).map h) =
    (proj).map h ≫ (proj).map g ≫ (c Y Z).inv ↔ _
  rw [Category.assoc, ← (proj).map_id Y, c_inv_map, ← Category.assoc,
    ← Functor.map_comp, ← Category.assoc ((proj).map h), ← Functor.map_comp, cancel_mono]

theorem uniformity_of_factorization {A B D : Q} (h : A ⟶ D)
    (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D) (s : D ⟶ B ⨿ A)
    (hf : f = h ≫ s) (hg : g = s ≫ coprod.map (𝟙 B) h) :
    iterateChosen Seed f = h ≫ iterateChosen Seed g := by
  rw [hf, hg]
  exact iterateChosen_roll Seed h s

theorem uniformity_of_iso {A B D : Q} (h : A ≅ D)
    (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h.hom = h.hom ≫ g) :
    iterateChosen Seed f = h.hom ≫ iterateChosen Seed g := by
  apply uniformity_of_factorization Seed h.hom f g (h.inv ≫ f)
  · rw [Iso.hom_inv_id_assoc]
  · rw [Category.assoc, comm, Iso.inv_hom_id_assoc]

theorem uniformity_of_constructor_square {A B D : P} {h : A ⟶ D}
    (hh : Paper.TypeCategory.ConstructorReturn h) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g) :
    iterateChosen Seed (projectStep Seed f) = (proj).map h ≫ iterateChosen Seed (projectStep Seed g) := by
  rw [iterateChosen_projectStep Seed, iterateChosen_projectStep Seed, ← Functor.map_comp]
  exact congrArg (proj).map (Paper.TypeCategory.iterate_uniformity_ofConstructorReturn hh f g comm)

theorem guardedElgot :
    letI := Paper.Extension.Singleton.guardedIteration Seed
    ElgotCategory Q := by
  let := Paper.Extension.Singleton.guardedIteration Seed
  exact ⟨iterateChosen_fixpoint Seed, iterateChosen_naturality Seed, iterateChosen_codiagonal Seed⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedElgot
