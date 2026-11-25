module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Projection.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms

/-! # Projection after iteration with a retained factor -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Paper.TypeCategory.Projection (productSnd)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IterationProjection

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

private theorem productSnd_natural (Z : Comp) {A B : Comp} (f : A ⟶ B) :
    whiskerLeft Z f ≫ productSnd Z B = productSnd Z A ≫ f :=
  whiskerLeft_productSnd (show τ from Z) f

theorem iterate_productSnd (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    Paper.TypeCategory.iterate (whiskerLeft Z f ≫ (leftCoproductComparisonIso Z B A).inv) ≫ productSnd Z B =
      productSnd Z A ≫ Paper.TypeCategory.iterate f := by
  rw [whiskerLeft_iterate, productSnd_natural]

theorem iterate_projected_whiskerLeft (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    Paper.TypeCategory.iterate
      ((whiskerLeft Z f ≫ (leftCoproductComparisonIso Z B A).inv) ≫
        coprod.map (productSnd Z B) (𝟙 (tensorObj Z A))) =
      productSnd Z A ≫ Paper.TypeCategory.iterate f := by
  rw [← iterate_naturality, iterate_productSnd]

set_option backward.isDefEq.respectTransparency false in
private theorem distribute_productSnd (Z A B : Comp) :
    (leftCoproductComparisonIso Z A B).inv ≫ coprod.map (productSnd Z A) (productSnd Z B) =
      productSnd Z (A ⨿ B) := by
  let e := leftCoproductComparisonIso Z A B
  apply (cancel_epi e.hom).mp
  change e.hom ≫ e.inv ≫ _ = e.hom ≫ _
  rw [Iso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_map]
    have h : (coprod.inl : tensorObj Z A ⟶ tensorObj Z A ⨿ tensorObj Z B) ≫ e.hom =
        whiskerLeft Z (coprod.inl : A ⟶ A ⨿ B) := by
      dsimp only [e]
      rw [leftCoproductComparisonIso_hom]
      exact inl_coprodComparison (whiskerLeftFunctor Z) A B
    rw [← Category.assoc _ e.hom, h, productSnd_natural]
  · rw [coprod.inr_map]
    have h : (coprod.inr : tensorObj Z B ⟶ tensorObj Z A ⨿ tensorObj Z B) ≫ e.hom =
        whiskerLeft Z (coprod.inr : B ⟶ A ⨿ B) := by
      dsimp only [e]
      rw [leftCoproductComparisonIso_hom]
      exact inr_coprodComparison (whiskerLeftFunctor Z) A B
    rw [← Category.assoc _ e.hom, h, productSnd_natural]

set_option backward.isDefEq.respectTransparency false in
theorem projected_whiskerLeft_square (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    ((whiskerLeft Z f ≫ (leftCoproductComparisonIso Z B A).inv) ≫
      coprod.map (productSnd Z B) (𝟙 (tensorObj Z A))) ≫ coprod.map (𝟙 B) (productSnd Z A) =
      productSnd Z A ≫ f := by
  have h : coprod.map (productSnd Z B) (𝟙 (tensorObj Z A)) ≫ coprod.map (𝟙 B) (productSnd Z A) =
      coprod.map (productSnd Z B) (productSnd Z A) := by
    apply coprod.hom_ext <;> simp
  rw [Category.assoc, h, Category.assoc, distribute_productSnd, productSnd_natural]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IterationProjection
