module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.TypeChange.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.ValidatedCaseAlgebra

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (InstructionModel)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

theorem expand_ofPresentation_proof (K : CoherentRegionModel J P)
    (A : CaseAlgebra P) (h : K.caseAlgebra = A) :
    (ofPresentation K A h).expand = K := by
  change expandFreyd J K.types (readInstructions J K.types A _) _ = K
  suffices ∀ (I : InstructionModel J K.types P.Instr), I = K.instructions →
      ∀ (coherent : letI := I; RegionTypingCoherent (Φ := P.Instr) J K.types),
        expandFreyd J K.types I coherent = K from
    this _ (readInstructions_of_presentation A _ K.instructions h) _
  intro I e coherent
  cases e
  cases K
  rfl

end Silmaril.Isotope.Institution.Acyclic.ValidatedCaseAlgebra
