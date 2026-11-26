module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Model.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Model

/-! # Model agreement for explicit and elaborated LetCase UB -/

public section

namespace Silmaril.Isotope.Institution.Refinement.UB.LetCase

open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory (TypingIndex)

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
variable {P : InstrSig τ ε} {e : ε} {Γ : Ctx ν τ}

/-- Evaluating canonical elaboration in a native ordered algebra agrees with
the induced explicit interpretation at every typing sort. -/
theorem encode_eval (M : OrderedAlgebra (dialectSignature P e Γ).sig)
    {i : TypingIndex τ} (a : Explicit P Γ i) :
    (dialectSignature P e Γ).eval M.toAlgebra (encode P e Γ a) =
      (adjoin (casePSig P.Instr Γ)).eval (explicitModel P e Γ M).toAlgebra a :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.encode_eval M a

/-- Native models of the interpreted axioms induce models of the explicit axioms. -/
theorem explicitModel_valid (axioms : Set (Sentence (casePSig P.Instr Γ)))
    (M : OrderedAlgebra (dialectSignature P e Γ).sig)
    (hM : M ∈ (institution.obj (interpretedSpec P e Γ axioms).sig).modelsOf
      (interpretedSpec P e Γ axioms).axioms) :
    explicitModel P e Γ M ∈ (institution.obj (explicitSpec P Γ axioms).sig).modelsOf
      (explicitSpec P Γ axioms).axioms :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.explicitModel_valid axioms M hM

/-- The Boolean occurrence model interprets the canonical spelling as the
greatest element of each carrier. -/
theorem flag_ub (i : TypingIndex τ) :
    (dialectSignature P e Γ).eval (flagModel P e Γ).toAlgebra (nativeUB P e Γ i) =
      ULift.up true :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.flag_ub i

/-- The occurrence model validates the transported original axioms and all the
native UB inequalities. The inherited sentences only mention old terms. -/
theorem flagModel_valid (axioms : Set (Sentence (casePSig P.Instr Γ))) :
    flagModel P e Γ ∈ (institution.obj (interpretedSpec P e Γ axioms).sig).modelsOf
      (interpretedSpec P e Γ axioms).axioms :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.flagModel_valid axioms

end Silmaril.Isotope.Institution.Refinement.UB.LetCase
