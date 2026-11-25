module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Reification.Iteration.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms

/-! # Carried iteration in the projection-return quotient -/

public section

universe u v u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.TypeCategory (ofType ofRegion sumIso diagonalArrow whiskerRight whiskerLeft)
open Paper.RetainedLet (returnOnce_typed)
open Paper.RetainedCase (reindexHom)
open Paper.SingletonReification
  (packedPair packedDiagonal packedWhiskerRight reindexValueHom reindexValueHom_comp denoteSingleton_firstTerm)
open Paper.SingletonReification.SingleCfg
open Paper.WithProjectionReturns (Step fstTerm)
open Paper.WithProjectionReturns.Reification
open Paper.Extension.Singleton (ofRegion_eq_iff whiskerRightFunctor whiskerRight_map)
open CfgEta.TypeCategory (productFstBranches)
open CfgEta.TypeCategory.ConstructorReification (fstMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
set_option hygiene false in
local notation "F" => Paper.WithProjectionReturns.projection (τ := τ) (Φ := Φ)
local notation "Q" => Paper.Extension.Singleton.ofRegion Step

set_option backward.isDefEq.respectTransparency false in
theorem captureViaReturn_map (X S : τ) :
    (F).map (captureViaReturn (Φ := Φ) X S) = Q (duplicateCapture_typed X S) := by
  have h : Q (returnOnce_typed (fstTerm (Φ := Φ) X S)) = Q (productFstBranches X S) :=
    (ofRegion_eq_iff Step _ _).2 ((Step.fst X S).eqv)
  let P := product X S
  change (F).map (diagonalArrow P ≫ whiskerRight (ofRegion (returnOnce_typed (fstTerm X S))) (ofType P)) = _
  rw [Functor.map_comp, ← whiskerRight_map]
  refine (congrArg
    (fun f => (F).map (diagonalArrow P) ≫
      (whiskerRightFunctor Step ((F).obj (ofType P))).map f) h).trans ?_
  rw [whiskerRight_map, ← Functor.map_comp, duplicateCapture_arrow]

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)

set_option backward.isDefEq.respectTransparency false in
private theorem capturePrefix_map {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    (F).map (capturePrefix J M objIso X S) = Q (duplicateCapture_typed X S) := by
  let P := product X S
  let f := fstMap M X S
  have split : packedPair M P X P f (𝟙 (M.obj P)) =
      packedDiagonal M P ≫ packedWhiskerRight M P P X f := by
    simp only [packedPair, packedDiagonal, packedWhiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (CartesianMonoidalCategory.lift _ _) (f ▷ M.obj P),
      CartesianMonoidalCategory.lift_whiskerRight, Category.id_comp]
  have fst := cmp.fstProducer
  rw [denoteSingleton_firstTerm J M] at fst
  change (F).map (reindexValueHom J M objIso P X f) = _ at fst
  change (F).map (reindexValueHom J M objIso P (product X P) (packedPair M P X P f (𝟙 _))) = _
  rw [split, reindexValueHom_comp, Functor.map_comp, cmp.diagonal, cmp.fstWhisker, fst, whiskerRight_map]
  rw [← Functor.map_comp]
  exact captureViaReturn_map X S

set_option backward.isDefEq.respectTransparency false in
theorem actualCarriedStep_map {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    (F).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (F).map (ofRegion (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom) := by
  rw [carriedStep_factor_retained, Functor.map_comp, Functor.map_comp,
    capturePrefix_map J M objIso cmp, cmp.block, cmp.route]
  simpa only [Category.assoc, Functor.map_comp] using
    congrArg (fun f => (F).map (f ≫ (sumIso (product X D) (product X S)).hom)) (realizePackedStep_arrow hb)

theorem actualCarriedIteration_map {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
    let state := paperCarrier J M objIso X S
    let result := paperCarrier J M objIso X D
    (F).map (state.inv ≫ Paper.TypeCategory.iterate actual ≫ result.hom) =
      Q (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  canonical_iterate_realize_map Step hb _ _ _ (actualCarriedStep_map J M objIso cmp)

theorem canonicalAssembly_actual_map {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    (F).map (canonicalAssembly (ofRegion he)
      (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType))) =
      Q (guardedCfg_typed he hb) := by
  refine (canonicalAssembly_map_congr Step rfl (actualCarriedStep_map J M objIso cmp)).trans ?_
  rw [canonicalAssembly_ofRegion]
  exact (ofRegion_eq_iff Step _ _).2 (.paper (canonicalRegion_eq_guardedCfg_realize he hb))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration
