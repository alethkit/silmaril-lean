module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Reification.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Thms

/-! Exercise the actual route on both packed exit tags. A repeat goes to the
right summand and a nested result goes to the left, with the capture retained. -/

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open scoped Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification.SingleCfg.Model (carriedRoute)
open Paper.WithProjectionReturnsAndUnitEta.Reification
open scoped Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.Extension.Singleton (ofType ofRegion sumIso sumCofan whiskerLeftFunctor whiskerLeft_map)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

private abbrev Flag : Ty Empty := .coprod .unit .unit
private abbrev Seed := Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
private abbrev F := Paper.WithProjectionReturnsAndUnitEta.projection (τ := Ty Empty) (Φ := Empty)
private abbrev C := Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := Ty Empty) (Φ := Empty)

local notation "L" => whiskerLeftFunctor Seed (ofType Seed Flag)
local notation "Tail" => Silmaril.coprod Flag (Silmaril.empty : Ty Empty)

set_option backward.isDefEq.respectTransparency false in
example {V : Type} [Category V] [CartesianMonoidalCategory V] [SymmetricCategory V]
    [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory C]
    (J : V ⥤ C) [DistributiveFreydCategory J] (M : TypeModel (Ty Empty) V)
    (objIso : ∀ A, J.obj (M.obj A) ≅ ofType Seed A)
    (carrierTensor : RetainedTensorAgrees J M objIso Flag Flag)
    (packed : RetainedPackedExitsAgree J M objIso Flag Flag Flag) :
    (L).map (sumCofan Seed Flag Tail).inl ≫ carriedRoute J M objIso Flag Flag Flag = coprod.inr ∧
      (L).map ((sumCofan Seed Flag Silmaril.empty).inl ≫ (sumCofan Seed Flag Tail).inr) ≫
        carriedRoute J M objIso Flag Flag Flag = coprod.inl := by
  let decoder := ofRegion Seed (exitDecoder_typed Flag Flag)
  let distributor := ofRegion Seed (distributorRegion_typed Flag Flag Flag)
  have shuffle : (L).map decoder ≫ distributor = ofRegion Seed (retagPacked_typed Flag Flag Flag) := by
    simpa only [Functor.map_comp, ← whiskerLeft_map] using!
      congrArg F.map (retagPacked_distributor (Φ := Empty) Flag Flag Flag)
  have repeatTag : (sumCofan Seed Flag Tail).inl ≫ decoder = (sumCofan Seed Flag Flag).inr := by
    simpa only [Functor.map_comp] using! congrArg F.map (exitDecoder_inl (Φ := Empty) Flag Flag)
  have resultTag : (sumCofan Seed Flag Silmaril.empty).inl ≫ (sumCofan Seed Flag Tail).inr ≫ decoder =
      (sumCofan Seed Flag Flag).inl := by
    simpa only [Functor.map_comp] using! congrArg F.map (exitDecoder_inr_inl (Φ := Empty) Flag Flag)
  have distribute := (Paper.RetainedCase.Chosen.projectedDistributor_eq_iff Seed Flag Flag Flag
    distributor).1 rfl
  rw [carriedRoute_eq_of_carrierTensor J M objIso Flag Flag Flag carrierTensor carrierTensor packed, ← shuffle]
  constructor
  · rw [← Category.assoc, ← Category.assoc, ← (L).map_comp, repeatTag, distribute.2,
      Paper.Extension.Singleton.sumCofan_inr_sumIso_hom]
    rfl
  · rw [← Category.assoc] at resultTag
    rw [← Category.assoc, ← Category.assoc, ← (L).map_comp, resultTag, distribute.1,
      Paper.Extension.Singleton.sumCofan_inl_sumIso_hom]
    rfl
