module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Thms

/-! # Strength of guarded feedback in contextual singleton quotients -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedIterationStrength

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.RetainedCase.Chosen (projectedChosenDistributor projectedChosenDistributor_inv)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "proj" => projection Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "L" => whiskerLeftFunctor Seed
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_iterateSum (X : τ) {A B : τ} (f : Obj A ⟶ Obj (B ⊕ₜ A)) :
    (L (Obj X)).map (iterateSum Seed f) =
      iterateSum Seed (A := X ×ₜ A) (B := X ×ₜ B)
        ((L (Obj X)).map f ≫ ofRegion Seed (distributorRegion_typed X B A)) := by
  obtain ⟨f₀, rfl⟩ := (proj).map_surjective (X := Paper.TypeCategory.ofType A)
    (Y := Paper.TypeCategory.ofType (B ⊕ₜ A)) f
  rw [iterateSum_map, whiskerLeft_map, whiskerLeft_map]
  change (proj).map _ = iterateSum Seed ((proj).map _ ≫
    (proj).map (Paper.TypeCategory.ofRegion (distributorRegion_typed X B A)))
  rw [← Functor.map_comp, iterateSum_map]
  exact congrArg (proj).map (Paper.TypeCategory.whiskerLeft_iterateSum X f₀)

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_iterateChosen (X : τ) {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    iterateChosen Seed
      ((L (Obj X)).map f ≫ (projectedChosenDistributor Seed X B A).inv) =
    (L (Obj X)).map (iterateChosen Seed f) := by
  let left := L (Obj X)
  let exactStep := f ≫ (sumIso Seed B A).inv
  have step :
      (left.map f ≫ (projectedChosenDistributor Seed X B A).inv) ≫
        (sumIso Seed (X ×ₜ B) (X ×ₜ A)).inv =
      left.map exactStep ≫ ofRegion Seed (distributorRegion_typed X B A) := by
    rw [projectedChosenDistributor_inv, show left.map exactStep =
      left.map f ≫ left.map (sumIso Seed B A).inv from left.map_comp _ _]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  change iterateSum Seed ((left.map f ≫ (projectedChosenDistributor Seed X B A).inv) ≫
    (sumIso Seed (X ×ₜ B) (X ×ₜ A)).inv) = left.map (iterateSum Seed exactStep)
  rw [step]
  exact (whiskerLeft_iterateSum Seed X exactStep).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedIterationStrength
