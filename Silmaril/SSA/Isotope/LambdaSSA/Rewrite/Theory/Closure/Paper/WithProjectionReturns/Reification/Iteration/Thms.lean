module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Reification.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration

/-! # Canonical carried iteration with projection returns -/

public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.TypeCategory (ofType ofRegion sumIso)
open Paper.SingletonReification.SingleCfg
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open SyntacticCategory (iterateRegion_valueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
set_option hygiene false in
local notation "F" => WithProjectionReturns.projection (τ := τ) (Φ := Φ)
local notation "Q" => Paper.Extension.Singleton.ofRegion Step

/-- The projection-return seed identifies the expression-based prefix with the
guarded capture in the extended quotient. -/
theorem captureViaReturn_map (X S : τ) :
    (F).map (captureViaReturn (Φ := Φ) X S) = Q (duplicateCapture_typed X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration.captureViaReturn_map X S

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)

/-- The actual chosen packed-block denotation contributes the explicit exact-sum
step in the projection-return quotient under the local factor comparisons. -/
theorem actualCarriedStep_map {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    (F).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (F).map (ofRegion (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration.actualCarriedStep_map J M objIso cmp

/-- Transport canonical iteration on the actual packed-block step through both
carriers. Its image is the guarded loop on the same explicit witness. -/
theorem actualCarriedIteration_map {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
    let state := paperCarrier J M objIso X S
    let result := paperCarrier J M objIso X D
    (F).map (state.inv ≫ Paper.TypeCategory.iterate actual ≫ result.hom) =
      Q (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration.actualCarriedIteration_map
    J M objIso cmp

/-- With the syntactic entry arrow and the actual carried block step, canonical
dispatch and iteration give the original guarded CFG arrow in the extension. -/
theorem canonicalAssembly_actual_map {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (cmp : CarriedStepComparisons J M objIso hb) :
    (F).map (canonicalAssembly (ofRegion he)
      (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType))) =
      Q (guardedCfg_typed he hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionCarriedIteration.canonicalAssembly_actual_map
    J M objIso he cmp

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification
