module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorMiddleNaturality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorPairs

/-! # The native syntactic triangle identity -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Inserting a unit in the left product and reassociating inserts the same
unit in the right product. This is the triangle before cancelling unitors. -/
theorem triangle_inverse_equates (A B : τ) :
    Equates (ε := ε) F R (input (product A B))
      (composeArrow (rightArrow (rightUnitInvArrow (F := F) (ε := ε) A) B) (assocArrow A Silmaril.unit B)).val
      (leftArrow A (leftUnitInvArrow (F := F) (ε := ε) B)).val (product A (product Silmaril.unit B)) := by
  let P := product A B
  let Γa := pairLeftContext P A B
  have da := leftParameter (F := F) (Φ := Φ) P A B (⊥ : ε)
  have db := rightParameter (F := F) (Φ := Φ) P A B (⊥ : ε)
  have du : HasType F Γa.zero (⊥ : ε) (.unit : Term Φ 3) Silmaril.unit :=
    .unit Γa.zero_discardable
  have hqa : quantity A ≤ Γa.linearity := by
    simp only [Γa, pairLeftContext, QCtx.linearity_snoc, Usage.linearity_zero,
      Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_rfl le_top)
  have hqb : quantity B ≤ (pairRightContext P A B).linearity := by
    simp only [pairRightContext, QCtx.linearity_snoc, Usage.linearity_zero,
      Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_rfl (le_inf le_top le_top)
  have hqu : quantity (Silmaril.unit : τ) ≤ Γa.zero.linearity := by
    rw [QCtx.zero_linearity]
    exact le_top
  have hbody := assoc_pair_equates (R := R) (pairSplit P A B) (QCtx.Split.zero_right Γa)
    da du db hqa hqu hqb
  have hd := HasType.pair (pairSplit P A B) (.pair (QCtx.Split.zero_right Γa) da.top du.top) db.top
  have hfirst := destruct_compose (R := R) hd (assocDeriv A Silmaril.unit B (⊤ : ε))
  have houter := Equates.let₂ (inputSplit P)
    (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hbody
  have h := hfirst.trans houter
  simpa only [composeArrow, composeTerm, rightArrow, rightTerm, rightUnitInvArrow,
    leftArrow, leftTerm, leftUnitInvArrow, assocArrow, onLeft, onRight, Tm.rename, Tm.up, Fin.cases_zero,
    continuation_atIndex, show (Fin.succ 0 : Fin 3) = 1 from rfl] using h

theorem triangle_inverse (hR : R.RenamingClosed) (A B : τ) :
    compose (ε := ε) (F := F) (R := R) hR
      (right hR (rightUnitInv A) B) (assoc A Silmaril.unit B) =
      left hR A (leftUnitInv B) :=
  Quotient.sound (triangle_inverse_equates A B)

/-- The associator and the two unitors satisfy the premonoidal triangle. -/
theorem triangle (hR : R.RenamingClosed) (A B : τ) :
    compose (ε := ε) (F := F) (R := R) hR
      (assoc A Silmaril.unit B) (left hR A (leftUnit B)) = right hR (rightUnit A) B := by
  have h := congrArg (fun f => compose hR f (left hR A (leftUnit B)))
    (triangle_inverse (F := F) (R := R) (ε := ε) hR A B)
  rw [← left_compose, leftUnitInv_leftUnit, left_identity] at h
  have h' := congrArg (compose hR (right hR (rightUnit A) B)) h
  rw [← compose_assoc, ← compose_assoc, ← compose_right,
    rightUnit_rightUnitInv, identity_right, identity_compose, compose_identity] at h'
  exact h'

end Silmaril.Isotope.Refinement.Models.Syntactic
