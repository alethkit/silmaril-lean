module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Syntax.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.Syntax

public section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory.Limits Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

universe u v

/-- Every algebra for the extended signature receives exactly one fold of explicit terms. -/
noncomputable def syntaxIsInitial {I : Type u} (S : TheoryModel.Signature.{u,v} I) :
    IsInitial (syntaxAlgebra S) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.syntaxIsInitial S

end Silmaril.Isotope.Institution.Refinement.UB
