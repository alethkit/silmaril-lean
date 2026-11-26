module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement

/-! # Preservation and reflection of LetCase refinement under UB elaboration -/

public section

namespace Silmaril.Isotope.Institution.Refinement.UB.LetCase

open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Isotope.LetCase.LocallyNameless (TypedRelation)

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
variable {P : InstrSig τ ε} {e : ε} {Γ : Ctx ν τ}

/-- Elaboration preserves and reflects the generated order. The target derivations may
use any exactly typed native intermediate; the compared endpoints have literal-unit UB. -/
theorem refinement_iff (axioms : Set (Sentence (casePSig P.Instr Γ))) {i : TypingIndex τ}
    (a b : Explicit P Γ i) :
    (explicitOrder P Γ axioms).Rel a b ↔
      (interpretedOrder P e Γ axioms).Rel (encode P e Γ a) (encode P e Γ b) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.refinement_iff axioms a b

/-- Quotienting by mutual refinement gives an order isomorphism at every
typing sort. The native quotient uses the restriction of the interpreted
order to terms in the literal-unit fragment. -/
noncomputable def quotientIso (axioms : Set (Sentence (casePSig P.Instr Γ))) (i : TypingIndex τ) :
    letI : Preorder (Explicit P Γ i) := (explicitOrder P Γ axioms).preorder i
    letI : Preorder {t : Native P e Γ i // Canonical P e Γ t} := canonicalPreorder P e Γ axioms i
    Antisymmetrization (Explicit P Γ i) (· ≤ ·) ≃o
      Antisymmetrization {t : Native P e Γ i // Canonical P e Γ t} (· ≤ ·) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.quotientIso axioms i

/-- Taking the inherited axioms from the original LetCase refinement theory
also gives preservation into the full native calculus with `nativeRules`. -/
theorem preserves_native (pureEff : ε) (R : TypedRelation ν P.Instr τ)
    {i : TypingIndex τ} (a b : Explicit P Γ i)
    (h : (explicitOrder P Γ (caseTheory pureEff Γ R).sentences).Rel a b) :
    nativeRefines P e pureEff Γ R (encode P e Γ a) (encode P e Γ b) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase.preserves_native pureEff R a b h

end Silmaril.Isotope.Institution.Refinement.UB.LetCase
