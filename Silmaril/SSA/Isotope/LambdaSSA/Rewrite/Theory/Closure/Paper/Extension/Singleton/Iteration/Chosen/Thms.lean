module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedIterationStrength

/-! # Exact and chosen-sum strength of projected guarded feedback -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen (projectedChosenDistributor)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained (distributorRegion_typed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Obj" => ofType (Φ := Φ) Seed
local notation "L" => whiskerLeftFunctor Seed
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

/-- Feedback commutes with retaining a factor using the literal distributor on exact sums. -/
theorem whiskerLeft_iterateSum (X : τ) {A B : τ} (f : Obj A ⟶ Obj (B ⊕ₜ A)) :
    (L (Obj X)).map (iterateSum Seed f) =
      iterateSum Seed (A := X ×ₜ A) (B := X ×ₜ B)
        ((L (Obj X)).map f ≫ ofRegion Seed (distributorRegion_typed X B A)) :=
  ProjectedIterationStrength.whiskerLeft_iterateSum Seed X f

/-- The same equation at the chosen coproducts, using the transported guarded distributor. -/
theorem whiskerLeft_iterateChosen (X : τ) {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    iterateChosen Seed ((L (Obj X)).map f ≫ (projectedChosenDistributor Seed X B A).inv) =
      (L (Obj X)).map (iterateChosen Seed f) :=
  ProjectedIterationStrength.whiskerLeft_iterateChosen Seed X f

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
