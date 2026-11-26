module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCapturedRecurExit

/-! # Reify the carried block that repeats once from its left phase -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton (ofType ofRegion sumIso)
open Paper.SingletonReification.SingleCfg (blockComputation realizePackedStep_typed)
open Paper.SingletonReification.SingleCfg.Model (carrier)
open Paper.SingletonReification.SingleCfg.CapturedRecurExit (Flag Carry blockBound)
open scoped Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open SyntacticCategory (iterateRegion_valueBranches)

universe u v

local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := Ty Empty) (Φ := Empty)
local notation "Obj" => ofType (Seed)
local notation "Lit" => ofRegion (Seed)

/-- The guarded step updates the left phase to the right phase and returns
from the right phase. Its two-step unrolling is independent of the tail. -/
theorem capturedRecurExit_unroll_two :
    ∃ out : Obj Carry ⟶ Obj Carry, ∀ tail,
      unroll (Lit (realizePackedStep_typed blockBound) ≫ (sumIso (Seed) Carry Carry).hom) tail 2 = out :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCapturedRecurExit.capturedRecurExit_unroll_two

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Empty]
  (objIso : ∀ A, J.obj (M.obj A) ≅ Obj A)

-- The interpreted distributivity and iteration are parameters even at this concrete quotient.
set_option linter.concreteInstances false in
/-- Reify the interpreted captured loop after checking the usual local
step comparisons. The two constructor phases determine its iteration. -/
theorem actualCarriedIteration_eq_capturedRecurExit
    (cmp : CarriedStepComparisons J M objIso blockBound) :
    let actual := contextualStep J (blockComputation M J Flag Flag Flag
      (denoteSingletonRegion J M blockBound.hasType))
    let state := carrier J M objIso Flag Flag
    state.inv ≫ CategoryTheory.iterate actual ≫ state.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed blockBound)) := by
  obtain ⟨out, finite⟩ := capturedRecurExit_unroll_two
  exact actualCarriedIteration_eq_of_boundedRealization J M objIso cmp 2 out finite

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
