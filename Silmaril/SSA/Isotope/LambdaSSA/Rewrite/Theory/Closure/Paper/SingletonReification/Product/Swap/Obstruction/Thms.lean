module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Thms

/-! # Local model obstructions for the instruction-free Paper quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory Paper.BoundSimulation.Obstruction
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (braid ofType ofRegion)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (fstTerm)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v

local notation "Comp" => Paper.TypeCategory (τ := Ty Empty) Empty
local notation "U" => (Ty.unit : Ty Empty)

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp] [HasFiniteCoproducts Comp]
  [DistributivePremonoidalCategory Comp] [Iteration Comp] [ElgotCategory Comp]
  (J : V ⥤ Comp) [StrongElgotFreydCategory J] (M : TypeModel (Ty Empty) V)
  [InstructionModel J M Empty] [RegionTypingCoherent (Φ := Empty) J M]
  (objIso : ∀ T : Ty Empty, J.obj (M.obj T) ≅ ofType (Φ := Empty) T)

set_option linter.concreteInstances false in
/-- The producer and guarded first-projection comparisons at the product of
two units are incompatible in the default instruction-free Paper quotient. -/
theorem producer_fst_comparisons_incompatible
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Empty) U U)).hasType) =
        ofRegion (returnOnce_typed (fstTerm (Φ := Empty) U U)))
    (fst : reindexValueHom J M objIso (product U U) U (fstMap M U U) =
      ofRegion (productFstBranches (Φ := Empty) U U)) : False :=
  Paper.BoundSimulation.Obstruction.fst_return_fails
    (projection_comparisons_force_return J M objIso U U producer fst)

set_option linter.concreteInstances false in
/-- The mixed swap comparison conflicts with the local swap-term producer
comparison in the same quotient. -/
theorem producer_mixed_swap_comparisons_incompatible
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (swapTerm_typed (Φ := Empty) (product U U) U)).hasType) =
        ofRegion (returnOnce_typed (swapTerm_typed (Φ := Empty) (product U U) U)))
    (swap : reindexValueHom J M objIso (product (product U U) U) (product U (product U U))
      (packedSwap M (product U U) U) = braid (product U U) U) : False :=
  Paper.BoundSimulation.Obstruction.mixed_swap_return_fails
    ((compare_swap_iff_return J M objIso (product U U) U producer).1 swap)

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
