module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.RetainedElimination

/-! # Native coassociativity of quantity-permitted duplication -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem copy_assoc_equates (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    Equates (ε := ε) F R (input A)
      (composeArrow (copyArrow (F := F) (ε := ε) A hA)
        (composeArrow (rightArrow (copyArrow A hA) A) (assocArrow A A A))).val
      (composeArrow (copyArrow (F := F) (ε := ε) A hA) (leftArrow A (copyArrow A hA))).val
      (product A (product A A)) := by
  have s := input_diagonal A hA
  have di := identityDeriv (F := F) (Φ := Φ) A (⊥ : ε)
  have dc := copyDeriv (F := F) (Φ := Φ) A hA (⊥ : ε)
  have hid := identity_compose_equates (ε := ε) (F := F) R (copyArrow A hA)
  simp only [composeArrow, composeTerm, identityArrow, copyArrow, continuation_atIndex] at hid
  have hleft := (pair_then_right (R := R) s di.top di dc.top
    (by rw [input_linearity])).trans (Equates.pair s hid (Equates.refl ⟨di.top⟩))
  have hright := (pair_then_left_any (R := R) s di.top di.top dc.top).trans
    (Equates.pair s (Equates.refl ⟨di.top⟩) hid)
  have hassoc := assoc_pair_equates (R := R) s s di di di
    (by rw [input_linearity]) (by rw [input_linearity]) (by rw [input_linearity])
  have h := (action_compose (R := R) dc.top (rightDeriv A dc.top)
    (assocDeriv A A A (⊤ : ε))).trans
    ((action_congr hleft (assocDeriv A A A (⊤ : ε))).trans (hassoc.trans hright.symm))
  simpa only [composeArrow, composeTerm, copyArrow, rightArrow, leftArrow, assocArrow,
    continuation_atIndex, action] using h

theorem copy_assoc (hR : R.RenamingClosed) (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    compose (ε := ε) (F := F) (R := R) hR (copy A hA)
      (compose hR (right hR (copy A hA) A) (assoc A A A)) =
      compose hR (copy A hA) (left hR A (copy A hA)) :=
  Quotient.sound (copy_assoc_equates A hA)

end Silmaril.Isotope.Refinement.Models.Syntactic
