module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Thms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Injection equations for the transported distributors -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ChosenDistributor

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedCase.Chosen (paperChosenDistributor projectedChosenDistributor)
open scoped MonoidalCategory

section Transport

universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {A B : C} [HasBinaryCoproduct A B] (L : C ⥤ D) [HasBinaryCoproduct (L.obj A) (L.obj B)]

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonFromCofans_hom
    (src : BinaryCofan A B) (dst : BinaryCofan (L.obj A) (L.obj B))
    (s : src.pt ≅ A ⨿ B) (t : dst.pt ≅ L.obj A ⨿ L.obj B) (d : L.obj src.pt ≅ dst.pt)
    (hsl : src.inl ≫ s.hom = coprod.inl) (hsr : src.inr ≫ s.hom = coprod.inr)
    (htl : dst.inl ≫ t.hom = coprod.inl) (htr : dst.inr ≫ t.hom = coprod.inr)
    (hl : L.map src.inl ≫ d.hom = dst.inl) (hr : L.map src.inr ≫ d.hom = dst.inr) :
    (t.symm ≪≫ d.symm ≪≫ L.mapIso s).hom = coprodComparison L A B := by
  apply coprod.hom_ext
  · rw [inl_coprodComparison]
    change coprod.inl ≫ (t.inv ≫ d.inv ≫ L.map s.hom) = L.map coprod.inl
    rw [← htl, ← hsl, Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← hl]
  · rw [inr_coprodComparison]
    change coprod.inr ≫ (t.inv ≫ d.inv ≫ L.map s.hom) = L.map coprod.inr
    rw [← htr, ← hsr, Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← hr]

end Transport

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

section Base
open Paper.TypeCategory (ofType sumCofan sumIso whiskerLeftFunctor)
open Paper.RetainedCase (distributorIso distributorIso_hom left_distributor_inl left_distributor_inr)

theorem paperChosenDistributor_hom (X A B : τ) :
    (paperChosenDistributor (Φ := Φ) X A B).hom =
      coprodComparison (whiskerLeftFunctor (ofType (Φ := Φ) X)) (ofType A) (ofType B) := by
  refine comparisonFromCofans_hom (whiskerLeftFunctor (ofType X))
    (sumCofan A B) (sumCofan (product X A) (product X B))
    (sumIso A B) (sumIso (product X A) (product X B)) (distributorIso X A B)
    (Paper.TypeCategory.sumCofan_inl_sumIso_hom A B) (Paper.TypeCategory.sumCofan_inr_sumIso_hom A B)
    (Paper.TypeCategory.sumCofan_inl_sumIso_hom _ _) (Paper.TypeCategory.sumCofan_inr_sumIso_hom _ _) ?_ ?_
  · rw [distributorIso_hom]
    exact left_distributor_inl X A B
  · rw [distributorIso_hom]
    exact left_distributor_inr X A B

open CfgEta.TypeCategory.Retained (distributorRegion_typed)

set_option backward.isDefEq.respectTransparency false in
theorem paperChosenDistributor_inv (X A B : τ) :
    (paperChosenDistributor (Φ := Φ) X A B).inv =
      (whiskerLeftFunctor (ofType (Φ := Φ) X)).map (sumIso A B).inv ≫
        Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B) ≫
        (sumIso (product X A) (product X B)).hom := by
  change ((whiskerLeftFunctor (ofType (Φ := Φ) X)).map (sumIso A B).inv ≫
    (distributorIso X A B).hom) ≫ (sumIso (product X A) (product X B)).hom = _
  rw [Category.assoc, distributorIso_hom]

end Base

section Extension
open Paper.Extension.Singleton
open Paper.Extension.Singleton.CoproductDistributivity (leftTensorFunctor)
open Paper.RetainedCase (distributorIso distributorIso_hom left_distributor_inl left_distributor_inr)

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "F" => projection Seed
set_option hygiene false in
local notation "L" => whiskerLeftFunctor Seed

set_option backward.isDefEq.respectTransparency false in
theorem projectedChosenDistributor_hom (X A B : τ) :
    (projectedChosenDistributor Seed X A B).hom =
      coprodComparison (L (ofType Seed X)) (ofType Seed A) (ofType Seed B) := by
  refine comparisonFromCofans_hom (L (ofType Seed X))
    (sumCofan Seed A B) (sumCofan Seed (product X A) (product X B))
    (sumIso Seed A B) (sumIso Seed (product X A) (product X B)) ((F).mapIso (distributorIso X A B))
    (sumCofan_inl_sumIso_hom Seed A B) (sumCofan_inr_sumIso_hom Seed A B)
    (sumCofan_inl_sumIso_hom Seed _ _) (sumCofan_inr_sumIso_hom Seed _ _) ?_ ?_
  · change (L (ofType Seed X)).map ((F).map (Paper.TypeCategory.sumCofan A B).inl) ≫
      (F).map (distributorIso X A B).hom = (F).map (Paper.TypeCategory.sumCofan (product X A) (product X B)).inl
    rw [whiskerLeft_map, distributorIso_hom, ← Functor.map_comp, left_distributor_inl]
  · change (L (ofType Seed X)).map ((F).map (Paper.TypeCategory.sumCofan A B).inr) ≫
      (F).map (distributorIso X A B).hom = (F).map (Paper.TypeCategory.sumCofan (product X A) (product X B)).inr
    rw [whiskerLeft_map, distributorIso_hom, ← Functor.map_comp, left_distributor_inr]

set_option backward.isDefEq.respectTransparency false in
theorem leftIso_eq_projected [PremonoidalCategory (TypeCategory Seed)] [DistributiveTensor (TypeCategory Seed)]
    (X A B : τ) (e : L (ofType Seed X) ≅ leftTensorFunctor Seed (ofType Seed X)) :
    DistributiveTensor.leftIso (ofType Seed X) (ofType Seed A) (ofType Seed B) =
      coprod.mapIso (e.app (ofType Seed A)).symm (e.app (ofType Seed B)).symm ≪≫
        projectedChosenDistributor Seed X A B ≪≫ e.app (ofType Seed A ⨿ ofType Seed B) := by
  apply Iso.ext
  change coprodComparison (leftTensorFunctor Seed (ofType Seed X)) (ofType Seed A) (ofType Seed B) = _
  apply coprod.hom_ext
  · simp only [Iso.trans_hom, coprod.mapIso, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      coprod.inl_map_assoc, inl_coprodComparison,
      projectedChosenDistributor_hom, inl_coprodComparison_assoc, e.hom.naturality]
    simp
  · simp only [Iso.trans_hom, coprod.mapIso, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      coprod.inr_map_assoc, inr_coprodComparison,
      projectedChosenDistributor_hom, inr_coprodComparison_assoc, e.hom.naturality]
    simp

set_option backward.isDefEq.respectTransparency false in
theorem chosenDistributor_projection (X A B : τ) :
    (PreservesColimitPair.iso (F) (Paper.TypeCategory.ofType (product X A))
      (Paper.TypeCategory.ofType (product X B))).hom ≫ (F).map (paperChosenDistributor X A B).hom =
    (projectedChosenDistributor Seed X A B).hom ≫
      (L (ofType Seed X)).map
        (PreservesColimitPair.iso (F) (Paper.TypeCategory.ofType A) (Paper.TypeCategory.ofType B)).hom := by
  rw [projectedChosenDistributor_hom, paperChosenDistributor_hom,
    PreservesColimitPair.iso_hom, PreservesColimitPair.iso_hom]
  let AX := Paper.TypeCategory.ofType (Φ := Φ) A
  let BX := Paper.TypeCategory.ofType (Φ := Φ) B
  let K := Paper.TypeCategory.whiskerLeftFunctor (Paper.TypeCategory.ofType (Φ := Φ) X)
  change coprodComparison (F) (K.obj AX) (K.obj BX) ≫ (F).map (coprodComparison K AX BX) =
    coprodComparison (L (ofType Seed X)) ((F).obj AX) ((F).obj BX) ≫
      (L (ofType Seed X)).map (coprodComparison (F) AX BX)
  let N := L (ofType Seed X)
  have h₁ : coprod.inl ≫ coprodComparison N ((F).obj AX) ((F).obj BX) ≫
      N.map (coprodComparison (F) AX BX) = N.map ((F).map coprod.inl) := by
    rw [inl_coprodComparison_assoc, ← N.map_comp, inl_coprodComparison]
  have h₂ : coprod.inr ≫ coprodComparison N ((F).obj AX) ((F).obj BX) ≫
      N.map (coprodComparison (F) AX BX) = N.map ((F).map coprod.inr) := by
    rw [inr_coprodComparison_assoc, ← N.map_comp, inr_coprodComparison]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc (F) (K.obj AX) (K.obj BX),
      ← (F).map_comp, inl_coprodComparison K AX BX]
    exact (whiskerLeft_map Seed _).symm.trans h₁.symm
  · rw [inr_coprodComparison_assoc (F) (K.obj AX) (K.obj BX),
      ← (F).map_comp, inr_coprodComparison K AX BX]
    exact (whiskerLeft_map Seed _).symm.trans h₂.symm

open Paper.Extension.Singleton.CoproductDistributivity (whiskeredSumIsColimit)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

set_option backward.isDefEq.respectTransparency false in
theorem projectedChosenDistributor_inv (X A B : τ) :
    (projectedChosenDistributor Seed X A B).inv =
      (L (ofType Seed X)).map (sumIso Seed A B).inv ≫
        ofRegion Seed (distributorRegion_typed X A B) ≫
        (sumIso Seed (product X A) (product X B)).hom := by
  change ((L (ofType Seed X)).map (sumIso Seed A B).inv ≫
    (F).map (distributorIso X A B).hom) ≫ (sumIso Seed (product X A) (product X B)).hom = _
  rw [Category.assoc, distributorIso_hom]

set_option backward.isDefEq.respectTransparency false in
theorem projectedDistributor_eq_iff (X A B : τ)
    (g : ofType Seed (product X (Silmaril.coprod A B)) ⟶
      ofType Seed (Silmaril.coprod (product X A) (product X B))) :
    g = ofRegion Seed (distributorRegion_typed X A B) ↔
      (L (ofType Seed X)).map (sumCofan Seed A B).inl ≫ g =
        (sumCofan Seed (product X A) (product X B)).inl ∧
      (L (ofType Seed X)).map (sumCofan Seed A B).inr ≫ g =
        (sumCofan Seed (product X A) (product X B)).inr := by
  have hl : (L (ofType Seed X)).map (sumCofan Seed A B).inl ≫
      ofRegion Seed (distributorRegion_typed X A B) = (sumCofan Seed (product X A) (product X B)).inl := by
    change (L (ofType Seed X)).map ((F).map (Paper.TypeCategory.sumCofan A B).inl) ≫
      (F).map (Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B)) = _
    rw [whiskerLeft_map, ← Functor.map_comp, left_distributor_inl]
    rfl
  have hr : (L (ofType Seed X)).map (sumCofan Seed A B).inr ≫
      ofRegion Seed (distributorRegion_typed X A B) = (sumCofan Seed (product X A) (product X B)).inr := by
    change (L (ofType Seed X)).map ((F).map (Paper.TypeCategory.sumCofan A B).inr) ≫
      (F).map (Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B)) = _
    rw [whiskerLeft_map, ← Functor.map_comp, left_distributor_inr]
    rfl
  refine ⟨fun h => h.symm ▸ ⟨hl, hr⟩, fun h => ?_⟩
  exact BinaryCofan.IsColimit.hom_ext (whiskeredSumIsColimit Seed X A B) (h.1.trans hl.symm) (h.2.trans hr.symm)

end Extension

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ChosenDistributor
