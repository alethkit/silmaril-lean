module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Model.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration

/-! # Actual carried reification in the projection-return and unit-η quotient -/

public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (sumIso sumCofan whiskerLeft whiskerLeftFunctor whiskerRight diagonalArrow)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (packedWhiskerRight packedWhiskerLeft packedDiagonal)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
  (guardedCfg_typed realizePackedStep_typed blockComputation retagPacked_typed exitSum exitDecoder_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model
  (reindexHom carrier packedTensorIso carriedRoute)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained (packedDistributor)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap inlMap inrMap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (fstTerm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open _root_.Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Seed)
set_option hygiene false in
local notation "Lit" => Paper.Extension.Singleton.ofRegion (Seed)

/-- The first projection return and its guarded representative agree in the joined quotient. -/
theorem fstReturn_eq (X S : τ) :
    Lit (returnOnce_typed (fstTerm (Φ := Φ) X S)) = Lit (productFstBranches X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.fstReturn_eq X S

/-- Canonical assembly of the guarded factors gives the original one-block CFG. -/
theorem canonicalAssembly_ofRegion {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    canonicalAssembly (Lit he) (Lit (realizePackedStep_typed hb)) = Lit (guardedCfg_typed he hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.canonicalAssembly_ofRegion he hb

section Retained

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  (J : V ⥤ Comp) [DistributiveFreydCategory J] (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The native right whisker comparison follows from endpoint tensor agreement and centrality of the value map. -/
theorem reindexPackedWhiskerRight_of_tensorIso {R A B : τ} (f : M.obj A ⟶ M.obj B)
    (source : (packedTensorIso J M objIso A R).hom =
      (J.obj (M.obj A) ◁ (objIso R).hom) ≫ ((objIso A).hom ▷ Obj R))
    (target : (packedTensorIso J M objIso B R).hom =
      (J.obj (M.obj B) ◁ (objIso R).hom) ≫ ((objIso B).hom ▷ Obj R)) :
    reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
      reindexHom J M objIso (J.map f) ▷ Obj R :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.reindexPackedWhiskerRight_of_tensorIso J M objIso f source target

/-- Retained computation agrees with the native left whisker under the two tensor comparisons and the displayed local interchange. -/
theorem reindexRetainLeft_of_tensorIso {R A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B))
    (source : (packedTensorIso J M objIso R A).hom =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ (objIso A).hom))
    (target : (packedTensorIso J M objIso R B).hom =
      ((objIso R).hom ▷ J.obj (M.obj B)) ≫ (Obj R ◁ (objIso B).hom))
    (swap : (J.obj (M.obj R) ◁ f) ≫ ((objIso R).hom ▷ J.obj (M.obj B)) =
      ((objIso R).hom ▷ J.obj (M.obj A)) ≫ (Obj R ◁ f)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) f ≫
      J.map (M.productIso R B).inv) =
      Obj R ◁ reindexHom J M objIso f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.reindexRetainLeft_of_tensorIso J M objIso f source target swap

/-- Compare the carried route using the retained decoder and two pairs of injection equations.
The output equations compare the interpreted sum injections. The input equations
test the interpreted distributor on the two native left-whiskered injections. -/
theorem carriedRoute_of_distributor_injections (X S D : τ)
    (outputInl :
      reindexHom J M objIso (J.map (inlMap M (product X D) (product X S))) =
        (sumCofan (Seed) (product X D) (product X S)).inl)
    (outputInr :
      reindexHom J M objIso (J.map (inrMap M (product X D) (product X S))) =
        (sumCofan (Seed) (product X D) (product X S)).inr)
    (decoder :
      reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) =
        whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)))
    (inputInl :
      (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inl ≫
          reindexHom J M objIso (J.map (packedDistributor M X D S)) =
        (sumCofan (Seed) (product X D) (product X S)).inl)
    (inputInr :
      (whiskerLeftFunctor (Seed) (Obj X)).map (sumCofan (Seed) D S).inr ≫
          reindexHom J M objIso (J.map (packedDistributor M X D S)) =
        (sumCofan (Seed) (product X D) (product X S)).inr) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.carriedRoute_of_distributor_injections
    J M objIso X S D outputInl outputInr decoder inputInl inputInr

/-- Once the distributor and chosen output sum agree, the exact remaining
comparison is left retention of the packed exit decoder. -/
theorem carriedRoute_eq_iff_retainedDecoder (X S D : τ)
    (coordinates : CarriedDistributorCoordinates J M objIso X S D) :
    (carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom) ↔
    reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) =
      whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.carriedRoute_eq_iff_retainedDecoder
    J M objIso X S D coordinates

/-- Derive the carried route from the distributor coordinates and the packed
decoder's repeat and result tags and retained source coordinates. -/
theorem carriedRoute_eq_of_coordinates (X S D : τ)
    (coordinates : CarriedDistributorCoordinates J M objIso X S D)
    (packedSum : SumInjectionsAgree J M objIso S (coprod D Silmaril.empty))
    (resultTag :
      reindexHom J M objIso (J.map (inlMap M D Silmaril.empty)) = (sumCofan (Seed) D Silmaril.empty).inl)
    (packedTensor : RetainedTensorAgrees J M objIso X (packedExitType [S, D])) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.carriedRoute_eq_of_coordinates
    J M objIso X S D coordinates packedSum resultTag packedTensor

/-- Compare the retained decoder using the coproduct coordinates induced by the packed exit tags. -/
theorem retainedExitDecoder_eq_of_packedExitIso (X S D : τ)
    (exits : SumInjectionsAgree J M objIso D S)
    (target : RetainedTensorAgrees J M objIso X (coprod D S))
    (packed : RetainedPackedExitsAgree J M objIso X S D) :
    reindexHom J M objIso (J.map (packedWhiskerLeft M X (packedExitType [S, D]) (coprod D S) (exitSum M S D))) =
      whiskerLeft (Seed) (Obj X) (Lit (exitDecoder_typed S D)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.retainedExitDecoder_eq_of_packedExitIso
    J M objIso X S D exits target packed

/-- Compare the actual route using the induced packed exit and chosen output sums. -/
theorem carriedRoute_eq_of_packedExitIso (X S D : τ)
    (exits : SumInjectionsAgree J M objIso D S)
    (tensorState : RetainedTensorAgrees J M objIso X S)
    (tensorResult : RetainedTensorAgrees J M objIso X D)
    (tensorExits : RetainedTensorAgrees J M objIso X (coprod D S))
    (packed : RetainedPackedExitsAgree J M objIso X S D) :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.carriedRoute_eq_of_packedExitIso
    J M objIso X S D exits tensorState tensorResult tensorExits packed

end Retained

section Model

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The actual first-projection return comparison reduces to the reindexed value projection. -/
theorem fstProducer_denote_iff [RegionTypingCoherent (Φ := Φ) J M] (X S : τ) :
    (reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) X S)).hasType) =
      Lit (returnOnce_typed (fstTerm X S))) ↔
    reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.fstProducer_denote_iff J M objIso X S

/-- The five local comparisons identify the actual reindexed block step with its guarded representative. -/
theorem actualCarriedStep_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    actualCarriedStep J M objIso hb =
      Lit (realizePackedStep_typed hb) ≫ (sumIso (Seed) (product X D) (product X S)).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.actualCarriedStep_eq J M objIso cmp

/-- The descended guarded iterator on the actual reindexed step agrees with the guarded loop. -/
theorem canonicalIterate_actual_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    canonicalIterate (actualCarriedStep J M objIso hb) =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.canonicalIterate_actual_eq J M objIso cmp

/-- The same representative compares with the transported model iteration under its named local agreement. -/
theorem actualCarriedIteration_eq {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb)
    (iteration : TransportedIterationAgrees J M objIso hb) :
    let actual := contextualStep J (Paper.SingletonReification.SingleCfg.blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X D
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.actualCarriedIteration_eq J M objIso cmp iteration

/-- Reify the actual transported iteration from local route coordinates and the
remaining comparisons at the block and its iterator. -/
theorem actualCarriedIteration_eq_of_route_coordinates {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (coordinates : CarriedDistributorCoordinates J M objIso X S D)
    (packedSum : SumInjectionsAgree J M objIso S (coprod D Silmaril.empty))
    (resultTag :
      reindexHom J M objIso (J.map (inlMap M D Silmaril.empty)) = (sumCofan (Seed) D Silmaril.empty).inl)
    (packedTensor : RetainedTensorAgrees J M objIso X (packedExitType [S, D]))
    (fstProducer :
      reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S))
    (diagonal : let P := product X S
      reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P))
    (fstWhisker : let P := product X S
      reindexHom J M objIso (J.map (packedWhiskerRight M P P X (fstMap M X S))) =
        whiskerRight (Seed) (reindexHom J M objIso (J.map (fstMap M X S))) (Obj P))
    (block : let P := product X S
      let K := packedExitType [S, D]
      reindexHom J M objIso (J.map (M.productIso X P).hom ≫
        retainLeft J (R := M.obj X) (denoteSingletonRegion J M hb.hasType) ≫
          J.map (M.productIso X K).inv) = whiskerLeft (Seed) (Obj X) (Lit hb))
    (iteration : TransportedIterationAgrees J M objIso hb) :
    let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X D
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  actualCarriedIteration_eq J M objIso
    ⟨fstProducer, diagonal, fstWhisker, block,
      carriedRoute_eq_of_coordinates J M objIso X S D coordinates packedSum resultTag packedTensor⟩
    iteration

/-- Reify the actual transported iteration using the induced packed exit and chosen output sums. -/
theorem actualCarriedIteration_eq_of_packedExitIso {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (exits : SumInjectionsAgree J M objIso D S)
    (tensorState : RetainedTensorAgrees J M objIso X S)
    (tensorResult : RetainedTensorAgrees J M objIso X D)
    (tensorExits : RetainedTensorAgrees J M objIso X (coprod D S))
    (packed : RetainedPackedExitsAgree J M objIso X S D)
    (fstProducer :
      reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S))
    (diagonal : let P := product X S
      reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P))
    (fstWhisker : let P := product X S
      reindexHom J M objIso (J.map (packedWhiskerRight M P P X (fstMap M X S))) =
        whiskerRight (Seed) (reindexHom J M objIso (J.map (fstMap M X S))) (Obj P))
    (block : let P := product X S
      let K := packedExitType [S, D]
      reindexHom J M objIso (J.map (M.productIso X P).hom ≫
        retainLeft J (R := M.obj X) (denoteSingletonRegion J M hb.hasType) ≫
          J.map (M.productIso X K).inv) = whiskerLeft (Seed) (Obj X) (Lit hb))
    (iteration : TransportedIterationAgrees J M objIso hb) :
    let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X D
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  actualCarriedIteration_eq J M objIso
    ⟨fstProducer, diagonal, fstWhisker, block,
      carriedRoute_eq_of_packedExitIso J M objIso X S D exits tensorState tensorResult tensorExits packed⟩
    iteration

/-- Canonical assembly uses the actual block denotation and the given syntactic entry. -/
theorem canonicalAssembly_actual_eq {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    canonicalAssembly (Lit he)
      (actualCarriedStep J M objIso hb ≫ (sumIso (Seed) (product X D) (product X S)).inv) =
      Lit (guardedCfg_typed he hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedIteration.canonicalAssembly_actual_eq J M objIso he cmp

/-- An actual interpreted entry can also be used once its local representative is identified. -/
theorem canonicalAssembly_denotations_eq {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (entry : reindexHom J M objIso (denoteSingletonRegion J M he.hasType) = Lit he)
    (cmp : CarriedStepComparisons J M objIso hb) :
    canonicalAssembly (reindexHom J M objIso (denoteSingletonRegion J M he.hasType))
      (actualCarriedStep J M objIso hb ≫ (sumIso (Seed) (product X D) (product X S)).inv) =
      Lit (guardedCfg_typed he hb) := by
  rw [entry]
  exact canonicalAssembly_actual_eq J M objIso he cmp

end Model

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
