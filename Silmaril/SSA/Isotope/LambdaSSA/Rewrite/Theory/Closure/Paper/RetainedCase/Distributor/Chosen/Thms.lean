module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ChosenDistributor

/-! # Exact and chosen coproduct comparisons for guarded distributivity -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

section Base
open Paper.TypeCategory (ofType sumIso whiskerLeftFunctor)

/-- Native Paper left whiskering has the chosen coproduct comparison as this forward map. -/
theorem paperChosenDistributor_hom (X A B : τ) :
    (paperChosenDistributor (Φ := Φ) X A B).hom =
      coprodComparison (whiskerLeftFunctor (ofType (Φ := Φ) X)) (ofType A) (ofType B) :=
  ChosenDistributor.paperChosenDistributor_hom X A B

/-- The inverse comparison runs the literal guarded distributor between the two sum conversions. -/
theorem paperChosenDistributor_inv (X A B : τ) :
    (paperChosenDistributor (Φ := Φ) X A B).inv =
      (whiskerLeftFunctor (ofType (Φ := Φ) X)).map (sumIso A B).inv ≫
        Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B) ≫
        (sumIso (product X A) (product X B)).hom :=
  ChosenDistributor.paperChosenDistributor_inv X A B

end Base

section Extension
open Paper.Extension.Singleton
open Paper.Extension.Singleton.CoproductDistributivity (leftTensorFunctor)

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "F" => projection Seed
set_option hygiene false in
local notation "L" => whiskerLeftFunctor Seed

/-- The projected forward map is the chosen coproduct comparison. -/
theorem projectedChosenDistributor_hom (X A B : τ) :
    (projectedChosenDistributor Seed X A B).hom =
      coprodComparison (L (ofType Seed X)) (ofType Seed A) (ofType Seed B) :=
  ChosenDistributor.projectedChosenDistributor_hom Seed X A B

/-- The inverse runs the image of the literal guarded distributor. -/
theorem projectedChosenDistributor_inv (X A B : τ) :
    (projectedChosenDistributor Seed X A B).inv =
      (L (ofType Seed X)).map (sumIso Seed A B).inv ≫
        ofRegion Seed (distributorRegion_typed X A B) ≫
        (sumIso Seed (product X A) (product X B)).hom :=
  ChosenDistributor.projectedChosenDistributor_inv Seed X A B

/-- The quotient projection commutes with the two chosen distributor comparisons. -/
theorem chosenDistributor_projection (X A B : τ) :
    (PreservesColimitPair.iso (F) (Paper.TypeCategory.ofType (product X A))
      (Paper.TypeCategory.ofType (product X B))).hom ≫ (F).map (paperChosenDistributor X A B).hom =
    (projectedChosenDistributor Seed X A B).hom ≫
      (L (ofType Seed X)).map
        (PreservesColimitPair.iso (F) (Paper.TypeCategory.ofType A) (Paper.TypeCategory.ofType B)).hom :=
  ChosenDistributor.chosenDistributor_projection Seed X A B

/-- When a premonoidal structure uses the same whisker up to natural isomorphism,
its chosen distributor is the transported guarded one. -/
theorem leftIso_eq_projected [PremonoidalCategory (Paper.Extension.Singleton.TypeCategory Seed)]
    [DistributiveTensor (Paper.Extension.Singleton.TypeCategory Seed)]
    (X A B : τ) (e : L (ofType Seed X) ≅ leftTensorFunctor Seed (ofType Seed X)) :
    DistributiveTensor.leftIso (ofType Seed X) (ofType Seed A) (ofType Seed B) =
      coprod.mapIso (e.app (ofType Seed A)).symm (e.app (ofType Seed B)).symm ≪≫
        projectedChosenDistributor Seed X A B ≪≫ e.app (ofType Seed A ⨿ ofType Seed B) :=
  ChosenDistributor.leftIso_eq_projected Seed X A B e

/-- An arrow at the exact packed interfaces is the projected literal distributor
exactly when it preserves the two guarded injections. -/
theorem projectedDistributor_eq_iff (X A B : τ)
    (g : ofType Seed (product X (Silmaril.coprod A B)) ⟶
      ofType Seed (Silmaril.coprod (product X A) (product X B))) :
    g = ofRegion Seed (distributorRegion_typed X A B) ↔
      (L (ofType Seed X)).map (sumCofan Seed A B).inl ≫ g =
        (sumCofan Seed (product X A) (product X B)).inl ∧
      (L (ofType Seed X)).map (sumCofan Seed A B).inr ≫ g =
        (sumCofan Seed (product X A) (product X B)).inr :=
  ChosenDistributor.projectedDistributor_eq_iff Seed X A B g

end Extension

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen
