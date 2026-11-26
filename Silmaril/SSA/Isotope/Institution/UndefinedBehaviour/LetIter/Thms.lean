module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LetIter

/-! # Typed LetIter round trip -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Institution.Refinement.UB.LetIter

open Silmaril.Isotope.Theory (TypingIndex)

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
variable {P : InstrSig τ ε} {e : ε} {Γ : Ctx ν τ} {i : TypingIndex τ}

/-- Elaboration only uses literal unit as the operand of a fresh instruction. -/
theorem encode_canonical (t : Explicit P Γ i) : Canonical P e Γ (encode P e Γ t) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetIter.encode_canonical t

/-- Reading back the canonical elaboration recovers the original explicit term. -/
theorem decode_encode (t : Explicit P Γ i) :
    decode P e Γ ⟨encode P e Γ t, encode_canonical t⟩ = t :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetIter.decode_encode t

/-- Every canonically spelled native term comes from explicit syntax. -/
theorem canonical_surjective (t : Native P e Γ i) (h : Canonical P e Γ t) :
    ∃ a : Explicit P Γ i, encode P e Γ a = t :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetIter.canonical_surjective t h

/-- Explicit UB and its native LetIter spelling are inverse at every typing sort,
including under binders. -/
def typedEquiv (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :
    Explicit P Γ i ≃ {t : Native P e Γ i // Canonical P e Γ t} where
  toFun t := ⟨encode P e Γ t, encode_canonical t⟩
  invFun := decode P e Γ
  left_inv := decode_encode
  right_inv t := by
    obtain ⟨a, ha⟩ := canonical_surjective t.val t.property
    have ht : (⟨encode P e Γ a, encode_canonical a⟩ : {t : Native P e Γ i // Canonical P e Γ t}) = t :=
      Subtype.ext ha
    rw [← ht, decode_encode]

end Silmaril.Isotope.Institution.Refinement.UB.LetIter
