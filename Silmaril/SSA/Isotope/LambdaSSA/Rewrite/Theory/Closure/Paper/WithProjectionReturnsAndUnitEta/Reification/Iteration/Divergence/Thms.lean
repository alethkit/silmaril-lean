module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Divergence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence

/-! # Compare the selected divergence of a repeat-only carried step -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton (ofType emptyIsInitial)
open Paper.RetainedLet (returnOnce_typed)
open Paper.SingletonReification.SingleCfg (blockComputation carriedIso)
open Paper.SingletonReification.SingleCfg.Model (carrier)
open CfgEta.TypeCategory.ConstructorReification (inlMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep retainEnvironment)
open CartesianMonoidalCategory (fst)

universe u v u₁ v₁

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)
set_option hygiene false in
local notation "Zero" => Obj (Silmaril.empty : τ)
set_option hygiene false in
local notation "fromZero" => (emptyIsInitial (Seed)).to
set_option hygiene false in
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

/-- Agreement at the empty exit is equivalent to agreement at every exit
for the same repeat-only transition. -/
theorem repeatDivergence_iff [Iteration Comp] [ElgotCategory Comp] {A X : Comp}
    (state : A ≅ X) (next : A ⟶ A) :
    RepeatDivergenceAgrees state next ↔
      ∀ B : Comp,
        state.inv ≫ CategoryTheory.iterate (show A ⟶ B ⨿ A from next ≫ coprod.inr) =
          canonicalIterate (show X ⟶ B ⨿ X from (state.inv ≫ next ≫ state.hom) ≫ coprod.inr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.repeatDivergence_iff
    state next

/-- For guarded identity repeat the constructor discard reduces the empty-exit
arrow to the one out of unit. -/
theorem guardedIdentityRepeat_factorsThroughUnit (A : τ) :
    canonicalIterate (coprod.inr : Obj A ⟶ Zero ⨿ Obj A) =
      (F).map (Paper.TypeCategory.discardArrow (Φ := Φ) A) ≫
        canonicalIterate (coprod.inr : Obj (Silmaril.unit : τ) ⟶ Zero ⨿ Obj (Silmaril.unit : τ)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.guardedIdentityRepeat_factorsThroughUnit
    A

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V)

/-- Value uniformity gives the same reduction to unit for the model iterator. -/
theorem modelIdentityRepeat_factorsThroughUnit (A : V) :
    CategoryTheory.iterate (coprod.inr : J.obj A ⟶ Zero ⨿ J.obj A) =
      J.map (CartesianMonoidalCategory.toUnit A ≫ M.unitIso.inv) ≫
        CategoryTheory.iterate (coprod.inr : J.obj (M.obj (Silmaril.unit : τ)) ⟶
          Zero ⨿ J.obj (M.obj (Silmaril.unit : τ))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.modelIdentityRepeat_factorsThroughUnit
    J M A

variable (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A) in
/-- A checked discard coordinate and agreement at unit suffice for an identity repeat. -/
theorem identityRepeat_agrees_of_unit {A : V} (B : τ)
    (state : J.obj A ≅ Obj B)
    (discard : state.inv ≫ J.map (CartesianMonoidalCategory.toUnit A ≫ M.unitIso.inv) ≫
        (objIso (Silmaril.unit : τ)).hom = (F).map (Paper.TypeCategory.discardArrow (Φ := Φ) B))
    (zero : RepeatDivergenceAgrees (objIso (Silmaril.unit : τ)) (𝟙 _)) :
    RepeatDivergenceAgrees state (𝟙 _) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.identityRepeat_agrees_of_unit
    J M objIso B state discard zero

variable [InstructionModel J M Φ]

/-- A block whose denotation produces only the packed repeat tag gives a repeat-only
contextual step. Its payload computation is executed before the next state. -/
theorem repeatStep_of_packed {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (payload : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj S))
    (tagged : denoteSingletonRegion J M hb.hasType =
      payload ≫ J.map (inlMap M S (coprod D Silmaril.empty))) :
    let E := ctxObj M [X]
    let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
    contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      retainEnvironment J (fst E (labelObj M [S])) f ≫ coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.repeatStep_of_packed
    J M hb payload tagged

variable [RegionTypingCoherent (Φ := Φ) J M] in
/-- The actual contextual step of the pure repeat block takes the repeat arm
with the identical carrier. -/
theorem repeatState_actualStep (X S D : τ) :
    contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M (repeatStateBlock (Φ := Φ) X S D).hasType)) = coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.repeatState_actualStep
    J M X S D

variable [RegionTypingCoherent (Φ := Φ) J M] in
/-- The term-returning repeat block executes the term as part of its next-state
computation, including any instruction calls in the term. -/
theorem repeatTerm_actualStep {X S D : τ} {t : Tm Φ} (ht : Tm.HasType [product X S] t S) :
    let E := ctxObj M [X]
    let payload := denoteSingletonRegion J M (returnOnce_typed ht).hasType
    let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
    contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M (repeatTermBlock ht).hasType)) =
        retainEnvironment J (fst E (labelObj M [S])) f ≫ coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.repeatTerm_actualStep
    J M ht

variable (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- At the actual result carrier, agreement is exactly equality of the two
empty-exit arrows after postcomposition with the unique outward map. -/
theorem transportedIterationAgrees_repeat_iff {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (next : J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [S]))
    (takesRepeat : contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      next ≫ coprod.inr) :
    let state := carrier J M objIso X S
    let out := (fromZero) (Obj (product X D))
    TransportedIterationAgrees J M objIso hb ↔
      (state.inv ≫ CategoryTheory.iterate (show _ ⟶ Zero ⨿ _ from next ≫ coprod.inr)) ≫ out =
        canonicalIterate (show _ ⟶ Zero ⨿ _ from (state.inv ≫ next ≫ state.hom) ≫ coprod.inr) ≫ out :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.transportedIterationAgrees_repeat_iff
    J M objIso hb next takesRepeat

/-- A comparison of the selected empty-exit arrows gives the transported
iteration comparison for a repeat-only block. -/
theorem transportedIterationAgrees_repeat_of_zero {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (next : J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [S]))
    (takesRepeat : contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      next ≫ coprod.inr)
    (zero : RepeatDivergenceAgrees (carrier J M objIso X S) next) :
    TransportedIterationAgrees J M objIso hb :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.transportedIterationAgrees_repeat_of_zero
    J M objIso hb next takesRepeat zero

variable [RegionTypingCoherent (Φ := Φ) J M] in
/-- For the actual pure repeat block, the only iterator comparison is the
selected divergence of the identity transition. -/
theorem transportedIterationAgrees_repeatState (X S D : τ)
    (zero : RepeatDivergenceAgrees (carrier J M objIso X S) (𝟙 _)) :
    TransportedIterationAgrees J M objIso (repeatStateBlock X S D) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence.transportedIterationAgrees_repeatState
    J M objIso X S D zero

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
