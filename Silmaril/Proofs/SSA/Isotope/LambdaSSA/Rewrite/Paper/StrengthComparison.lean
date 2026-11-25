module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms

/-! # The chosen coproduct comparison for the fixed-left-factor functor -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StrengthComparison

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

set_option backward.isDefEq.respectTransparency false

@[reassoc]
private theorem chosen_inl (Z X Y : Comp) :
    whiskerLeft Z (coprod.inl : X ⟶ X ⨿ Y) ≫ leftCoproductDistributor Z X Y =
      (coprod.inl : tensorObj Z X ⟶ tensorObj Z X ⨿ tensorObj Z Y) := by
  let z : τ := Z
  let x : τ := X
  let y : τ := Y
  have h : (coprod.inl : X ⟶ X ⨿ Y) ≫ (sumIso x y).inv = (sumCofan x y).inl := by
    rw [← sumCofan_inl_sumIso_hom x y, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change whiskerLeft Z (coprod.inl : X ⟶ X ⨿ Y) ≫
    (whiskerLeft Z (sumIso x y).inv ≫ ofRegion (τ := τ) (distributorRegion_typed z x y) ≫
      (sumIso (Silmaril.product z x) (Silmaril.product z y)).hom) = _
  rw [← Category.assoc, ← whiskerLeft_comp, h, ← Category.assoc, RetainedCase.left_distributor_inl,
    sumCofan_inl_sumIso_hom]
  rfl

@[reassoc]
private theorem chosen_inr (Z X Y : Comp) :
    whiskerLeft Z (coprod.inr : Y ⟶ X ⨿ Y) ≫ leftCoproductDistributor Z X Y =
      (coprod.inr : tensorObj Z Y ⟶ tensorObj Z X ⨿ tensorObj Z Y) := by
  let z : τ := Z
  let x : τ := X
  let y : τ := Y
  have h : (coprod.inr : Y ⟶ X ⨿ Y) ≫ (sumIso x y).inv = (sumCofan x y).inr := by
    rw [← sumCofan_inr_sumIso_hom x y, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change whiskerLeft Z (coprod.inr : Y ⟶ X ⨿ Y) ≫
    (whiskerLeft Z (sumIso x y).inv ≫ ofRegion (τ := τ) (distributorRegion_typed z x y) ≫
      (sumIso (Silmaril.product z x) (Silmaril.product z y)).hom) = _
  rw [← Category.assoc, ← whiskerLeft_comp, h, ← Category.assoc, RetainedCase.left_distributor_inr,
    sumCofan_inr_sumIso_hom]
  rfl

private theorem comparison_inl (Z X Y : Comp) :
    (coprod.inl : tensorObj Z X ⟶ tensorObj Z X ⨿ tensorObj Z Y) ≫
        coprodComparison (whiskerLeftFunctor Z) X Y =
      whiskerLeft Z (coprod.inl : X ⟶ X ⨿ Y) :=
  inl_coprodComparison (whiskerLeftFunctor Z) X Y

private theorem comparison_inr (Z X Y : Comp) :
    (coprod.inr : tensorObj Z Y ⟶ tensorObj Z X ⨿ tensorObj Z Y) ≫
        coprodComparison (whiskerLeftFunctor Z) X Y =
      whiskerLeft Z (coprod.inr : Y ⟶ X ⨿ Y) :=
  inr_coprodComparison (whiskerLeftFunctor Z) X Y

theorem comparison_hom_inv_id (Z X Y : Comp) :
    coprodComparison (whiskerLeftFunctor Z) X Y ≫ leftCoproductDistributor Z X Y =
      𝟙 (tensorObj Z X ⨿ tensorObj Z Y) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, comparison_inl]
    exact (chosen_inl Z X Y).trans
      (Category.comp_id (coprod.inl : tensorObj Z X ⟶ tensorObj Z X ⨿ tensorObj Z Y)).symm
  · rw [← Category.assoc, comparison_inr]
    exact (chosen_inr Z X Y).trans
      (Category.comp_id (coprod.inr : tensorObj Z Y ⟶ tensorObj Z X ⨿ tensorObj Z Y)).symm

theorem comparison_inv_hom_id (Z X Y : Comp) :
    leftCoproductDistributor Z X Y ≫ coprodComparison (whiskerLeftFunctor Z) X Y =
      𝟙 (tensorObj Z (X ⨿ Y)) := by
  let F := whiskerLeftFunctor Z
  let x : τ := X
  let y : τ := Y
  let e := F.mapIso (sumIso x y)
  apply (cancel_epi e.hom).1
  -- Compare on the exact tagged sum before transporting to the chosen coproduct.
  apply RetainedCase.distributor_hom_ext
  · have h : whiskerLeft Z (sumCofan x y).inl ≫ e.hom = whiskerLeft Z (coprod.inl : X ⟶ X ⨿ Y) := by
      change whiskerLeft Z (sumCofan x y).inl ≫ whiskerLeft Z (sumIso x y).hom = _
      rw [← whiskerLeft_comp, sumCofan_inl_sumIso_hom]
    rw [← Category.assoc, ← Category.assoc, h, Category.assoc, chosen_inl_assoc]
    exact (comparison_inl Z X Y).trans (h.symm.trans (by
      change whiskerLeft Z (sumCofan x y).inl ≫ whiskerLeft Z (sumIso x y).hom =
        whiskerLeft Z (sumCofan x y).inl ≫ whiskerLeft Z (sumIso x y).hom ≫ 𝟙 _
      rw [Category.comp_id]))
  · have h : whiskerLeft Z (sumCofan x y).inr ≫ e.hom = whiskerLeft Z (coprod.inr : Y ⟶ X ⨿ Y) := by
      change whiskerLeft Z (sumCofan x y).inr ≫ whiskerLeft Z (sumIso x y).hom = _
      rw [← whiskerLeft_comp, sumCofan_inr_sumIso_hom]
    rw [← Category.assoc, ← Category.assoc, h, Category.assoc, chosen_inr_assoc]
    exact (comparison_inr Z X Y).trans (h.symm.trans (by
      change whiskerLeft Z (sumCofan x y).inr ≫ whiskerLeft Z (sumIso x y).hom =
        whiskerLeft Z (sumCofan x y).inr ≫ whiskerLeft Z (sumIso x y).hom ≫ 𝟙 _
      rw [Category.comp_id]))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StrengthComparison
