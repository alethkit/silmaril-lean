module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Divergence.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Repeat.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Reduce a carried repeat-only endpoint to its selected empty exit -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.WithProjectionReturnsAndUnitEta.Reification
open scoped Paper.WithProjectionReturnsAndUnitEta.Reification
open Paper.Extension.Singleton
  (ofType emptyIsInitial iterateChosen_naturality projectStep uniformity_of_constructor_square)
open Paper.SingletonReification (denoteSingleton_snd_repeatTag)
open Paper.RetainedLet (returnOnce_typed)
open Paper.SingletonReification.SingleCfg (blockComputation carriedIso)
open Paper.SingletonReification.SingleCfg.Model
  (carrier contextualStep_repeat_of_packed contextualStep_identityRepeat_of_packed)
open CfgEta.TypeCategory.ConstructorReification (sndMap inlMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
  (labelInject_payload)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel contextualStep retainEnvironment)
open CategoryTheory.CartesianMonoidalCategory (fst)

universe u v u₁ v₁

theorem iterate_repeat_naturality {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [Iteration C] [ElgotCategory C] {A T B : C} (next : A ⟶ A) (g : T ⟶ B) :
    CategoryTheory.iterate (show A ⟶ T ⨿ A from next ≫ coprod.inr) ≫ g =
      CategoryTheory.iterate (show A ⟶ B ⨿ A from next ≫ coprod.inr) := by
  rw [ElgotCategory.naturality, Category.assoc, coprod.inr_map, Category.id_comp]

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
set_option hygiene false in
local notation "BaseObj" => Paper.TypeCategory.ofType (τ := τ) (Φ := Φ)

theorem canonicalIterate_repeat_naturality {A T B : Comp} (next : A ⟶ A) (g : T ⟶ B) :
    canonicalIterate (show A ⟶ T ⨿ A from next ≫ coprod.inr) ≫ g =
      canonicalIterate (show A ⟶ B ⨿ A from next ≫ coprod.inr) := by
  have h := iterateChosen_naturality (Seed) (show A ⟶ T ⨿ A from next ≫ coprod.inr) g
  rw [Category.assoc, coprod.inr_map, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem repeatDivergence_iff [Iteration Comp] [ElgotCategory Comp] {A X : Comp}
    (state : A ≅ X) (next : A ⟶ A) :
    RepeatDivergenceAgrees state next ↔
      ∀ B : Comp,
        state.inv ≫ CategoryTheory.iterate (show A ⟶ B ⨿ A from next ≫ coprod.inr) =
          canonicalIterate (show X ⟶ B ⨿ X from (state.inv ≫ next ≫ state.hom) ≫ coprod.inr) := by
  refine ⟨fun h B => ?_, fun h => h (Zero)⟩
  change state.inv ≫ CategoryTheory.iterate (show A ⟶ Zero ⨿ A from next ≫ coprod.inr) =
    canonicalIterate (show X ⟶ Zero ⨿ X from (state.inv ≫ next ≫ state.hom) ≫ coprod.inr) at h
  have map := congrArg (· ≫ (fromZero) B) h
  rw [Category.assoc, iterate_repeat_naturality, canonicalIterate_repeat_naturality] at map
  exact map

set_option backward.isDefEq.respectTransparency false in
private theorem project_repeat (A B : τ) :
    projectStep (Seed)
      (coprod.inr : (BaseObj A) ⟶ (BaseObj B) ⨿ (BaseObj A)) =
      (coprod.inr : Obj A ⟶ Obj B ⨿ Obj A) := by
  let c := PreservesColimitPair.iso (F) (BaseObj B) (BaseObj A)
  apply (cancel_mono c.hom).mp
  change ((F).map (coprod.inr : BaseObj A ⟶ BaseObj B ⨿ BaseObj A) ≫ c.inv) ≫ c.hom =
    coprod.inr ≫ c.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesColimitPair.iso_hom,
    inr_coprodComparison]

theorem guardedIdentityRepeat_factorsThroughUnit (A : τ) :
    canonicalIterate (coprod.inr : Obj A ⟶ Zero ⨿ Obj A) =
      (F).map (Paper.TypeCategory.discardArrow (Φ := Φ) A) ≫
        canonicalIterate (coprod.inr : Obj (Silmaril.unit : τ) ⟶ Zero ⨿ Obj (Silmaril.unit : τ)) := by
  let U : τ := Silmaril.unit
  let E : τ := Silmaril.empty
  let h := Paper.TypeCategory.discardArrow (Φ := Φ) A
  have value : Paper.TypeCategory.ConstructorReturn h := ⟨.unit, .unit, rfl⟩
  have square : (coprod.inr : BaseObj A ⟶ BaseObj E ⨿ BaseObj A) ≫ coprod.map (𝟙 (BaseObj E)) h =
      h ≫ (coprod.inr : BaseObj U ⟶ BaseObj E ⨿ BaseObj U) :=
    coprod.inr_map _ _
  have commutes := uniformity_of_constructor_square (Seed) value _ _ square
  rw [project_repeat, project_repeat] at commutes
  exact commutes

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

omit [InstructionModel J M Φ] in
theorem modelIdentityRepeat_factorsThroughUnit (A : V) :
    CategoryTheory.iterate (coprod.inr : J.obj A ⟶ Zero ⨿ J.obj A) =
      J.map (CartesianMonoidalCategory.toUnit A ≫ M.unitIso.inv) ≫
        CategoryTheory.iterate (coprod.inr : J.obj (M.obj (Silmaril.unit : τ)) ⟶
          Zero ⨿ J.obj (M.obj (Silmaril.unit : τ))) :=
  ElgotFreydCategory.pure_uniformity J coprod.inr coprod.inr
    (CartesianMonoidalCategory.toUnit A ≫ M.unitIso.inv) (coprod.inr_map _ _)


set_option backward.isDefEq.respectTransparency false in
theorem repeatStep_of_packed {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (payload : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj S))
    (tagged : denoteSingletonRegion J M hb.hasType =
      payload ≫ J.map (inlMap M S (coprod D Silmaril.empty))) :
    let E := ctxObj M [X]
    let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
    contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      retainEnvironment J (fst E (labelObj M [S])) f ≫ coprod.inr :=
  contextualStep_repeat_of_packed J M hb payload tagged

variable [RegionTypingCoherent (Φ := Φ) J M] in
set_option backward.isDefEq.respectTransparency false in
theorem repeatState_actualStep (X S D : τ) :
    contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M (repeatStateBlock (Φ := Φ) X S D).hasType)) = coprod.inr :=
  contextualStep_identityRepeat_of_packed J M (repeatStateBlock X S D)
    (denoteSingleton_snd_repeatTag J M X S D)

variable [RegionTypingCoherent (Φ := Φ) J M] in
set_option backward.isDefEq.respectTransparency false in
private theorem repeatTerm_tagged {X S D : τ} {t : Tm Φ} (ht : Tm.HasType [product X S] t S) :
    denoteSingletonRegion J M (repeatTermBlock (D := D) ht).hasType =
      denoteSingletonRegion J M (returnOnce_typed ht).hasType ≫
        J.map (inlMap M S (coprod D Silmaril.empty)) := by
  let P := product X S
  let K := packedExitType [S, D]
  let k := lookup M 0 (rfl : At [S, P] 0 S)
  let tag := inlMap M S (coprod D Silmaril.empty)
  let arg := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [S, P] 0 S)
  have value := RegionDenotes.let₁ (denote_spec J M ht)
    (RegionDenotes.br (h := (rfl : At [S] 0 S)) arg)
  have packed := RegionDenotes.let₁ (denote_spec J M ht)
    (RegionDenotes.br (h := (rfl : At [K] 0 K)) (Denotes.inl (B := coprod D Silmaril.empty) arg))
  unfold denoteSingletonRegion
  rw [← value.eq_denote J M, ← packed.eq_denote J M]
  change J.map (λ_ (M.obj P)).inv ≫ Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J (denote J M ht)
      ((J.map k ≫ J.map tag) ≫ J.map (labelInject M 0 (L := [K]) rfl)) ≫ J.map (singletonLabelPayload M K) =
    (J.map (λ_ (M.obj P)).inv ≫ Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J (denote J M ht)
      (J.map k ≫ J.map (labelInject M 0 (L := [S]) rfl)) ≫ J.map (singletonLabelPayload M S)) ≫ J.map tag
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc,
    ← J.map_comp, labelInject_payload, Category.comp_id]
  rw [labelInject_payload M K]
  exact congrArg (fun (a : ctxObj M [S, P] ⟶ M.obj K) =>
    J.map (λ_ (M.obj P)).inv ≫
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend J (denote J M ht) ≫ J.map a)
    (congrArg (k ≫ ·) (Category.comp_id tag))

variable [RegionTypingCoherent (Φ := Φ) J M] in
theorem repeatTerm_actualStep {X S D : τ} {t : Tm Φ} (ht : Tm.HasType [product X S] t S) :
    let E := ctxObj M [X]
    let payload := denoteSingletonRegion J M (returnOnce_typed ht).hasType
    let f := J.map (carriedIso M X S).hom ≫ payload ≫ J.map (labelInject M 0 (L := [S]) rfl)
    contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M (repeatTermBlock ht).hasType)) =
        retainEnvironment J (fst E (labelObj M [S])) f ≫ coprod.inr :=
  repeatStep_of_packed J M (repeatTermBlock ht) _ (repeatTerm_tagged J M (D := D) ht)


variable (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

set_option backward.isDefEq.respectTransparency false in
theorem transportedIterationAgrees_repeat_iff {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (next : J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [S]))
    (takesRepeat : contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      next ≫ coprod.inr) :
    let state := carrier J M objIso X S
    let out := (fromZero) (Obj (product X D))
    TransportedIterationAgrees J M objIso hb ↔
      (state.inv ≫ CategoryTheory.iterate (show _ ⟶ Zero ⨿ _ from next ≫ coprod.inr)) ≫ out =
        canonicalIterate (show _ ⟶ Zero ⨿ _ from (state.inv ≫ next ≫ state.hom) ≫ coprod.inr) ≫ out := by
  let state := carrier J M objIso X S
  let result := carrier J M objIso X D
  let out := (fromZero) (Obj (product X D))
  let rawOut := (fromZero) (J.obj (ctxObj M [X] ⊗ labelObj M [D]))
  have outEq : rawOut ≫ result.hom = out := (emptyIsInitial (Seed)).hom_ext _ _
  have target : actualCarriedStep J M objIso hb = (state.inv ≫ next ≫ state.hom) ≫ coprod.inr := by
    change state.inv ≫ contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) ≫
      coprod.map result.hom state.hom = _
    simp only [takesRepeat, Category.assoc, coprod.inr_map]
  have modelAtOut :
      state.inv ≫ CategoryTheory.iterate (show _ ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [D]) ⨿ _ from
        next ≫ coprod.inr) ≫ result.hom =
      (state.inv ≫ CategoryTheory.iterate (show _ ⟶ Zero ⨿ _ from next ≫ coprod.inr)) ≫ out := by
    rw [← iterate_repeat_naturality next rawOut, Category.assoc, Category.assoc, outEq]
  dsimp only [TransportedIterationAgrees]
  rw [takesRepeat, target, modelAtOut, ← canonicalIterate_repeat_naturality _ out]

set_option backward.isDefEq.respectTransparency false in
theorem transportedIterationAgrees_repeat_of_zero {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (next : J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [S]))
    (takesRepeat : contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      next ≫ coprod.inr)
    (zero : RepeatDivergenceAgrees (carrier J M objIso X S) next) :
    TransportedIterationAgrees J M objIso hb :=
  (transportedIterationAgrees_repeat_iff J M objIso hb next takesRepeat).2
    (congrArg (· ≫ (fromZero) (Obj (product X D))) zero)

variable [RegionTypingCoherent (Φ := Φ) J M] in
theorem transportedIterationAgrees_repeatState (X S D : τ)
    (zero : RepeatDivergenceAgrees (carrier J M objIso X S) (𝟙 _)) :
    TransportedIterationAgrees J M objIso (repeatStateBlock X S D) :=
  transportedIterationAgrees_repeat_of_zero J M objIso (repeatStateBlock X S D) (𝟙 _)
    (by simpa only [Category.id_comp] using repeatState_actualStep J M X S D) zero

omit [InstructionModel J M Φ] in
set_option backward.isDefEq.respectTransparency false in
theorem identityRepeat_agrees_of_unit {A : V} (B : τ)
    (state : J.obj A ≅ Obj B)
    (discard : state.inv ≫ J.map (CartesianMonoidalCategory.toUnit A ≫ M.unitIso.inv) ≫
        (objIso (Silmaril.unit : τ)).hom = (F).map (Paper.TypeCategory.discardArrow (Φ := Φ) B))
    (zero : RepeatDivergenceAgrees (objIso (Silmaril.unit : τ)) (𝟙 _)) :
    RepeatDivergenceAgrees state (𝟙 _) := by
  dsimp only [RepeatDivergenceAgrees] at zero ⊢
  simp only [Category.id_comp, Iso.inv_hom_id] at zero ⊢
  rw [modelIdentityRepeat_factorsThroughUnit J M A, guardedIdentityRepeat_factorsThroughUnit,
    ← discard, Category.assoc, ← zero]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRepeatDivergence
