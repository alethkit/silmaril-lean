module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.TypeChange.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.ExpansionTypeChange

/-! # The object-level expansion section commutes with type change -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.ValidatedCaseAlgebra

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory.TheoryModel
open Morphism (SignatureMap)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- Expansion is a section of the algebra reduct on the validated objects. -/
@[simp] theorem expand_caseAlgebra (A : ValidatedCaseAlgebra J P) :
    A.expand.caseAlgebra = A.algebra :=
  A.presentation

/-- When validation uses an existing model, readback recovers that model. -/
@[simp] theorem expand_ofPresentation (K : CoherentRegionModel J P)
    (A : CaseAlgebra P) (h : K.caseAlgebra = A) :
    (ofPresentation K A h).expand = K :=
  expand_ofPresentation_proof K A h

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

/-- The validated reduct keeps the algebra of the existing mapped presentation. -/
theorem reduct_algebra (A : ValidatedCaseAlgebra J Q) :
    (A.reduct g).algebra = Algebra.reductObj (PresSig.toHom (typeCaseHom g)) A.algebra :=
  rfl

/-- The carrier identification uses exactly the pulled-back type model. -/
theorem reduct_types (A : ValidatedCaseAlgebra J Q) :
    (A.reduct g).types = pullbackTypes g A.types :=
  rfl

/-- Reading back after algebra reduct gives the restricted primitive arrows,
with domains and codomains transported by the signature map. -/
theorem readInstructions_reduct (A : ValidatedCaseAlgebra J Q) :
    readInstructions J (pullbackTypes g A.types) (A.reduct g).algebra (A.reduct g).carriers =
      pullbackInstructions g A.expand.instructions :=
  readInstructions_of_presentation _ _ _ ((caseAlgebra_typeChange g A.expand).trans
    (congrArg (Algebra.reductObj (PresSig.toHom (typeCaseHom g))) A.presentation))

/-- Expanding after algebra reduct gives the same coherent region model as
expanding first and applying the existing witnessed SSA pullback. -/
theorem expand_reduct (A : ValidatedCaseAlgebra J Q) :
    (A.reduct g).expand = A.expand.pullbackOfWitness g (regionWitnessPullback g A.expand) :=
  expand_ofPresentation _ _ _

end Silmaril.Isotope.Institution.Acyclic.ValidatedCaseAlgebra
