module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Thms

/-! # Validated LetCase algebras and their dependent reduct -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory.TheoryModel
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

/-- An exact LetCase algebra with a chosen Freyd carrier identification and
normalized operation presentation whose readback is region-coherent. -/
structure ValidatedCaseAlgebra (P : InstrSig τ ε) where
  types : TypeModel τ V
  algebra : CaseAlgebra P
  carriers : algebra.Carrier = freydCaseArrow J types
  presentation : freydCaseAlgebra J types (readInstructions J types algebra carriers) = algebra
  coherent : letI := readInstructions J types algebra carriers
             RegionTypingCoherent (Φ := P.Instr) J types

variable {J}

namespace ValidatedCaseAlgebra

/-- Expand using the primitive arrows read from the validated algebra. -/
noncomputable def expand (A : ValidatedCaseAlgebra J P) : CoherentRegionModel J P :=
  expandAlgebra J A.types A.algebra A.carriers A.coherent

/-- An algebra equal to a coherent model's presentation is validated on the
model's chosen type interpretation. The input algebra is retained as a field. -/
noncomputable def ofPresentation (K : CoherentRegionModel J P)
    (A : CaseAlgebra P) (h : K.caseAlgebra = A) : ValidatedCaseAlgebra J P :=
  let presentation : freydCaseAlgebra J K.types K.instructions = A := h
  let carriers : A.Carrier = freydCaseArrow J K.types :=
    (congrArg (fun B : CaseAlgebra P => B.Carrier) presentation).symm
  have instructions := readInstructions_of_presentation A carriers K.instructions presentation
  let coherent (I : InstructionModel J K.types P.Instr) : Prop :=
    letI := I
    RegionTypingCoherent (Φ := P.Instr) J K.types
  { types := K.types
    algebra := A
    carriers := carriers
    presentation := (congrArg (freydCaseAlgebra J K.types) instructions).trans presentation
    coherent := cast (congrArg coherent instructions.symm) K.coherent }

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

/-- Restrict the chosen type model and use the actual LetCase algebra reduct
to supply the new algebra's operations. Forward region witness transport
validates this reduct in the pulled-back type interpretation. -/
noncomputable def reduct (A : ValidatedCaseAlgebra J Q) : ValidatedCaseAlgebra J P :=
  ofPresentation (A.expand.pullbackOfWitness g (regionWitnessPullback g A.expand))
    (Algebra.reductObj (PresSig.toHom (typeCaseHom g)) A.algebra)
    ((caseAlgebra_typeChange g A.expand).trans
      (congrArg (Algebra.reductObj (PresSig.toHom (typeCaseHom g))) A.presentation))

end ValidatedCaseAlgebra
end Silmaril.Isotope.Institution.Acyclic
