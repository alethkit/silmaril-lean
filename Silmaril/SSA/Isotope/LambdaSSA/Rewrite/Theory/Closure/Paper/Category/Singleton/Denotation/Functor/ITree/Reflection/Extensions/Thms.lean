module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Extensions.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeExtensions

/-! # Case returns and the remaining kernel at the same typed interface

The case-return seed resolves the term-case witness. A let inside a pair
gives a different equation that remains in the weak ITree kernel of the
case-return quotient. The latter separation uses the observer for all
three extra generators and their typed contextual closure.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection

open CategoryTheory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The case-return rule alone identifies the exact original representatives. -/
theorem termCase_eq_of_caseReturns :
    Paper.Extension.Eqv (Paper.WithCaseReturns.Step false) [Input] termCase regionCase [Output] :=
  SingletonFreeITreeExtensions.caseOnly

/-- The case-return quotient identifies the original arrows. The
projection-return and unit-η quotient separates them. -/
theorem termCase_quotient_boundary :
    caseProjection.map termArrow = caseProjection.map regionArrow ∧
      projectionUnit.map termArrow ≠ projectionUnit.map regionArrow :=
  ⟨SingletonFreeITreeExtensions.caseJoined, SingletonFreeITreeExtensions.projectionUnitDistinct⟩

/-- The ordinary weak tree image depends only on the class in the case-return
quotient, for every guarded arrow in this profile. -/
theorem image_eq_of_caseProjection_eq {A B : Ty Atom} (f g : ofType (Φ := Op) A ⟶ ofType B)
    (h : caseProjection.map f = caseProjection.map g) : interpretation.map f = interpretation.map g :=
  SingletonFreeITreeExtensions.image_eq_of_caseProjection_eq f g h

/-- Removing the unary identity let inside the pair preserves the weak
tree and changes the case-return quotient arrow. -/
theorem pair_quotient_separation :
    interpretation.map nestedPairArrow = interpretation.map plainPairArrow ∧
      caseProjection.map nestedPairArrow ≠ caseProjection.map plainPairArrow :=
  ⟨SingletonFreeITreeExtensions.pairsSameImage, SingletonFreeITreeExtensions.pairsDistinct⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection
