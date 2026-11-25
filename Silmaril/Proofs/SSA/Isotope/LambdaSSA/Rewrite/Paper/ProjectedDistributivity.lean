module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Exact distributivity descends through the contextual projection -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedDistributivity

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.Extension.Singleton.CoproductDistributivity (leftTensorFunctor)
open Paper.RetainedCase (distributorIso distributorIso_hom left_distributor_inl left_distributor_inr)
open scoped MonoidalCategory

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "Q" => TypeCategory Seed

set_option hygiene false in
local notation "P" => projection Seed
set_option hygiene false in
local notation "L" => whiskerLeftFunctor Seed

set_option backward.isDefEq.respectTransparency false in
noncomputable def whiskeredSumIsColimit (X A B : τ) :
    IsColimit (BinaryCofan.map ((L) (ofType Seed X)) (sumCofan Seed A B)) := by
  let e := (P).mapIso (distributorIso (Φ := Φ) X A B)
  apply (sumCofanIsColimit Seed (product X A) (product X B)).ofIsoColimit
  refine BinaryCofan.ext e.symm ?_ ?_
  · change (P).map (Paper.TypeCategory.sumCofan (product X A) (product X B)).inl =
      ((L) (ofType Seed X)).map ((P).map (Paper.TypeCategory.sumCofan A B).inl) ≫
        (P).map (distributorIso X A B).hom
    rw [whiskerLeft_map, distributorIso_hom, ← Functor.map_comp]
    exact congrArg (P).map (left_distributor_inl (Φ := Φ) X A B).symm
  · change (P).map (Paper.TypeCategory.sumCofan (product X A) (product X B)).inr =
      ((L) (ofType Seed X)).map ((P).map (Paper.TypeCategory.sumCofan A B).inr) ≫
        (P).map (distributorIso X A B).hom
    rw [whiskerLeft_map, distributorIso_hom, ← Functor.map_comp]
    exact congrArg (P).map (left_distributor_inr (Φ := Φ) X A B).symm

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeftPreservesBinary (X : TypeCategory Seed) :
    PreservesColimitsOfShape (Discrete WalkingPair) ((L) X) where
  preservesColimit {K} := by
    let A : τ := (K.obj ⟨WalkingPair.left⟩).as
    let B : τ := (K.obj ⟨WalkingPair.right⟩).as
    let T : τ := X.as
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) ((L) X) :=
      preservesColimit_of_preserves_colimit_cocone (sumCofanIsColimit Seed A B)
        (BinaryCofan.isColimitMapCoconeEquiv.symm (whiskeredSumIsColimit Seed T A B))
    exact preservesColimit_of_iso_diagram ((L) X) (diagramIsoPair K).symm

variable [PremonoidalCategory Q]

theorem distributiveTensor_of_whisker
    (agree : ∀ X : Q, Nonempty (whiskerLeftFunctor Seed X ≅ leftTensorFunctor Seed X)) :
    DistributiveTensor Q where
  left_isIso X Y Z := by
    let := whiskerLeftPreservesBinary Seed X
    obtain ⟨e⟩ := agree X
    let := preservesColimitsOfShape_of_natIso (J := Discrete WalkingPair) e
    change IsIso (coprodComparison (leftTensorFunctor Seed X) Y Z)
    infer_instance

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedDistributivity
