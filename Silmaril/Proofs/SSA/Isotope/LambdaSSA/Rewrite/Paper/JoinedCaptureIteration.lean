module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

/-! # Computing the carried iterator when its block returns immediately -/

public section

universe u v u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.WithProjectionReturnsAndUnitEta.Reification
open scoped Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.Extension.Singleton (ofType sumCofan sumIso iterateSum iterateSum_map sumCofan_inl_sumIso_hom)
open Paper.SingletonReification (denoteSingleton_let₂_resultTag denoteSingleton_productFst)
open Paper.SingletonReification.SingleCfg (blockComputation carriedIso)
open Paper.SingletonReification.SingleCfg.Model (carrier)
open CfgEta.TypeCategory.ConstructorReification (fstMap inlMap inrMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelAppendSplit_succ route_inl)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel contextualStep routeEnvironment retainEnvironment_map)
open CategoryTheory.CartesianMonoidalCategory (fst lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)
set_option hygiene false in
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalIterate_return {A B : τ} (f : Obj A ⟶ Obj B) :
    canonicalIterate (f ≫ coprod.inl) = f := by
  have joinedInl :
      (coprod.inl : Obj B ⟶ Obj B ⨿ Obj A) ≫ (sumIso (Seed) B A).inv = (sumCofan (Seed) B A).inl := by
    apply (cancel_mono (sumIso (Seed) B A).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, sumCofan_inl_sumIso_hom]
  have paperInl :
      (coprod.inl : Paper.TypeCategory.ofType (Φ := Φ) B ⟶ _) ≫
        (Paper.TypeCategory.sumIso (Φ := Φ) B A).inv = (Paper.TypeCategory.sumCofan (Φ := Φ) B A).inl := by
    apply (cancel_mono (Paper.TypeCategory.sumIso (Φ := Φ) B A).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Paper.TypeCategory.sumCofan_inl_sumIso_hom]
  induction f using Quot.ind with
  | mk f =>
    change iterateSum (Seed) (((F).map f ≫ coprod.inl) ≫ (sumIso (Seed) B A).inv) = (F).map f
    have e : ((F).map f ≫ (coprod.inl : Obj B ⟶ Obj B ⨿ Obj A)) ≫ (sumIso (Seed) B A).inv =
        (F).map f ≫ (sumCofan (Seed) B A).inl :=
      (Category.assoc _ _ _).trans (congrArg ((F).map f ≫ ·) joinedInl)
    refine (congrArg (iterateSum (Seed)) e).trans ?_
    change iterateSum (Seed) ((F).map f ≫ (F).map (Paper.TypeCategory.sumCofan (Φ := Φ) B A).inl) = _
    rw [← Functor.map_comp, iterateSum_map, ← paperInl, ← Category.assoc]
    have h : Paper.TypeCategory.iterate (f ≫ coprod.inl) = f := by
      rw [Paper.TypeCategory.iterate_fixpoint, Category.assoc, coprod.inl_desc, Category.comp_id]
    exact congrArg (F).map h

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem actualCarriedStep_carrier_square {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    (carrier J M objIso X S).hom ≫ actualCarriedStep J M objIso hb =
      contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) ≫
        coprod.map (carrier J M objIso X D).hom (carrier J M objIso X S).hom :=
  Iso.hom_inv_id_assoc _ _

set_option backward.isDefEq.respectTransparency false in
theorem transportedIterationAgrees_of_return {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (out : J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [D]))
    (step : contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      out ≫ coprod.inl) :
    TransportedIterationAgrees J M objIso hb := by
  let state := carrier J M objIso X S
  let result := carrier J M objIso X D
  let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
  have interpreted : CategoryTheory.iterate actual = out := by
    change CategoryTheory.iterate (contextualStep J
      (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))) = out
    rw [step, ElgotCategory.fixpoint, Category.assoc, coprod.inl_desc, Category.comp_id]
  have reindexed :
      actualCarriedStep J M objIso hb = (state.inv ≫ out ≫ result.hom) ≫ coprod.inl := by
    change state.inv ≫ actual ≫ coprod.map result.hom state.hom = _
    simp only [actual, step, Category.assoc, coprod.inl_map]
  change state.inv ≫ CategoryTheory.iterate actual ≫ result.hom = _
  rw [interpreted, reindexed, canonicalIterate_return]

variable [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem capture_block_returns (X S : τ) :
    blockComputation M J X S X
      (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType) =
    J.map ((carriedIso M X S).hom ≫ fstMap M X S ≫ labelInject M 0 (L := [X]) rfl ≫ coprod.inl) := by
  have h : denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType =
      J.map (fstMap M X S) ≫ J.map (inlMap M X Silmaril.empty ≫ inrMap M S (coprod X Silmaril.empty)) := by
    rw [denoteSingleton_let₂_resultTag J M X S X (.var (i := 1) rfl), denoteSingleton_productFst J M X S]
  rw [blockComputation, h]
  simp only [← J.map_comp, Category.assoc]
  simp only [packedExitType, inlMap, inrMap, unpackLabel, Category.assoc, Iso.inv_hom_id_assoc,
    coprod.inr_desc_assoc, coprod.inl_desc_assoc, labelInject_labelMap_assoc]
  exact congrArg (fun tag => J.map ((carriedIso M X S).hom ≫ fstMap M X S ≫ tag))
    (labelAppendSplit_succ M S (rfl : At [X] 0 X))

set_option backward.isDefEq.respectTransparency false in
theorem captureResult_actualStep (X S : τ) :
    contextualStep J (blockComputation M J X S X
      (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType)) =
      J.map (lift (fst (ctxObj M [X]) (labelObj M [S]))
        ((carriedIso M X S).hom ≫ fstMap M X S ≫ labelInject M 0 (L := [X]) rfl)) ≫ coprod.inl := by
  unfold contextualStep
  rw [capture_block_returns J M X S, retainEnvironment_map]
  let E := ctxObj M [X]
  let p := fst E (labelObj M [S])
  let f := (carriedIso M X S).hom ≫ fstMap M X S ≫ labelInject M 0 (L := [X]) rfl
  let i : labelObj M [X] ⟶ labelObj M [X] ⨿ labelObj M [S] := coprod.inl
  have routed : J.map (lift p (f ≫ i)) ≫ routeEnvironment J E (labelObj M [X]) (labelObj M [S]) =
      J.map (lift p f) ≫ coprod.inl := by
    rw [← CartesianMonoidalCategory.lift_whiskerLeft, J.map_comp_assoc]
    exact congrArg (J.map (lift p f) ≫ ·) (route_inl J)
  simpa only [p, E, f, i, Category.assoc] using! routed

theorem captureResult_transportedIterationAgrees (X S : τ) :
    TransportedIterationAgrees J M objIso (captureResultBlock (Φ := Φ) X S) :=
  transportedIterationAgrees_of_return J M objIso _ _ (captureResult_actualStep J M X S)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration
