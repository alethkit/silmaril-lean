module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Uniqueness.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Extensions.Defs

import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniquenessBoundary

/-! # The term-case boundary for the singleton generator proof -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Paper.WithProjectionReturnsAndUnitEta (Step)
open Paper.Extension.Singleton (sumCofan)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)

open Paper.TypeCategory.ITree.Reflection (Op Atom Output payload projectionUnit regionArrow termArrow)

local notation "FixtureSeed" => Step (τ := Ty Atom) (Φ := Op)
/-- The copair of the tag swap and primitive arm generates the region-case arrow.
The term-case arrow fails the corresponding left injection equation in the joined quotient. -/
theorem case_return_decomposition_boundary :
    let swap := exactCopair FixtureSeed (sumCofan FixtureSeed payload payload).inr
      (sumCofan FixtureSeed payload payload).inl
    let factor := exactCopair FixtureSeed swap (primitive Op.poll)
    Generated factor ∧ projectionUnit.map regionArrow = factor ∧
      (sumCofan FixtureSeed Output payload).inl ≫ projectionUnit.map termArrow ≠ swap :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedSingletonUniquenessBoundary.case_return_decomposition_boundary

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness
