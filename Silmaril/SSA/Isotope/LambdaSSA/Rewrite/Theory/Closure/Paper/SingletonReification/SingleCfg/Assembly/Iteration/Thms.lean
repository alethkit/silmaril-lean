module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Thms
public import Silmaril.SSA.Isotope.Calco2019.LambdaSSA.Thms

/-! # The retained iterator of an explicit one-block LambdaSSA representative -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel contextualStep retainEnvironment routeEnvironment)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)
open Silmaril.Isotope.Calco2019.LambdaSSA (contextualBody)
open Silmaril.Calco2019 (categoricalFixpoints ofLawfulMonad kleisli_iterate_eq)
open Paper.TypeCategory (ofType ofRegion sumIso)
open SyntacticCategory (iterateRegion_valueBranches)

section Ambient

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V)

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
/-- The retained step used in one-block assembly is the CALCO body, before
projecting the capture from the result. -/
theorem contextualStep_eq_calcoBody [DistributiveFreydCategory J] {E A B : V}
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualStep J body = contextualBody J body := by
  simp only [contextualStep, contextualBody, retainEnvironment, routeEnvironment, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The repeat arm of a guarded one-block CFG runs the CALCO iterator on the actual
packed local block. Both retained carriers still include the input capture. -/
theorem denote_guardedCfg_calco [InstructionModel J M Φ] [FreydCategory.CentralUnit J]
    [RegionTypingCoherent (Φ := Φ) J M] {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    denoteSingletonRegion J M (guardedCfg_typed he hb).hasType =
      let entry := denoteSingletonRegion J M he.hasType
      let body := blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)
      let E := ctxObj M [X]
      J.map ((λ_ (M.obj X)).inv) ≫
        caseWithContext J
          (J.map ((λ_ (M.obj X)).hom) ≫ entry ≫
            J.map (unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D]))
          (J.map (CartesianMonoidalCategory.snd E (labelObj M [D])))
          ((categoricalFixpoints C).iterate (contextualStep J body) trivial ≫
            J.map (CartesianMonoidalCategory.snd E (labelObj M [D]))) ≫
        J.map (singletonLabelPayload M D) := by
  rw [denote_guardedCfg J M he hb]
  dsimp only [assemble]
  rw [Silmaril.Isotope.Calco2019.LambdaSSA.contextualLoop_eq, ← contextualStep_eq_calcoBody J]
  rfl

end Ambient

section Kleisli

variable {τ : Type u} [TypeFormers τ]
  (m : Type u₁ → Type u₁) [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]

local notation "J" => Kleisli.Adjunction.toKleisli (ofTypeMonad m)

/-- At the actual carried step the Kleisli model uses the CALCO inherited sum,
with the canonical comparison from the selected computation coproduct. -/
theorem actualStep_kleisli_iterate (M : TypeModel τ (Type u₁)) (X S D : τ)
    (b : (J).obj (M.obj (product X S)) ⟶ (J).obj (M.obj (packedExitType [S, D]))) :
    let step := contextualStep J (blockComputation M J X S D b)
    CategoryTheory.iterate step =
      (ofLawfulMonad m).iteration.iterate (step ≫ (Kleisli.Type.coprodIsoSum m
        ((J).obj (ctxObj M [X] ⊗ labelObj M [D]))
        ((J).obj (ctxObj M [X] ⊗ labelObj M [S]))).hom) trivial :=
  kleisli_iterate_eq m _

end Kleisli

section Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable {X S D : τ} {b : Region Φ}
  (hb : ValueBranches [product X S] b [packedExitType [S, D]])
  {U W : Comp} (state : U ≅ ofType (product X S)) (result : W ≅ ofType (product X D))
  (step : U ⟶ W ⨿ U)
  (represents : reindexStep state result step =
    ofRegion (τ := τ) (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom)

include represents in
/-- Canonical Paper iteration on the carried model step has the guarded singleton
loop as its explicit representative, after the two carrier isomorphisms. -/
theorem canonical_iterate_realize :
    state.inv ≫ Paper.TypeCategory.iterate step ≫ result.hom =
      ofRegion (τ := τ) (iterateRegion_valueBranches (realizePackedStep_typed hb)) := by
  rw [canonical_reindex state result step, represents]
  change Paper.TypeCategory.iterateSum ((_ ≫ (sumIso _ _).hom) ≫ (sumIso _ _).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Paper.TypeCategory.iterateSum_ofRegion]

variable [HasFiniteCoproducts Comp] [Iteration Comp]

include represents in
/-- The exact local preservation law for an identified explicit step is equality of
the transported ambient iterator with that one typed guarded loop. -/
theorem preservesLoop_iff_iterate_realize :
    PreservesLoop step ↔
      state.inv ≫ CategoryTheory.iterate step ≫ result.hom =
        ofRegion (τ := τ) (iterateRegion_valueBranches (realizePackedStep_typed hb)) := by
  rw [← canonical_iterate_realize hb state result step represents,
    cancel_epi, cancel_mono]
  rfl

end Paper

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
