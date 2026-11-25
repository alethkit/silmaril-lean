module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Exchange
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SwapLaws

/-! # Naturality of the syntactic structural maps

The unitors commute with arbitrary computations. Their equations use only the
native beta and sequencing laws; no unrestricted interchange law is assumed.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Inserting a right unit is natural, before passage to the quotient. -/
theorem rightUnitInv_natural_equates {A B : τ} (a : Arrow (Φ := Φ) (ε := ε) F A B) :
    Equates (ε := ε) F R (input A)
      (composeArrow a (rightUnitInvArrow B)).val
      (composeArrow (rightUnitInvArrow A) (rightArrow a Silmaril.unit)).val
      (product B Silmaril.unit) := by
  obtain ⟨da⟩ := a.property
  have hleft := pair_left_bind_any (R := R) (inputSplit A).symm da (zeroUnitDeriv A (⊤ : ε))
  have hright := pair_then_right (R := R) (inputSplit A).symm
    (identityDeriv A (⊤ : ε)) (zeroUnitDeriv A (⊥ : ε)) da
    (by rw [zeroInput_linearity]; exact le_top)
  have hid := Equates.pair (inputSplit A).symm (identity_compose_equates R a)
    (Equates.refl (R := R) ⟨zeroUnitDeriv A (⊤ : ε)⟩)
  simp only [composeArrow, composeTerm, identityArrow, continuation_atIndex] at hid
  simpa only [composeArrow, composeTerm, rightUnitInvArrow, rightArrow,
    continuation_atIndex, atIndex, Tm.lift, Tm.rename] using hleft.symm.trans (hright.trans hid).symm

/-- Inserting a left unit is natural, before passage to the quotient. -/
theorem leftUnitInv_natural_equates {A B : τ} (a : Arrow (Φ := Φ) (ε := ε) F A B) :
    Equates (ε := ε) F R (input A)
      (composeArrow a (leftUnitInvArrow B)).val
      (composeArrow (leftUnitInvArrow A) (leftArrow Silmaril.unit a)).val
      (product Silmaril.unit B) := by
  obtain ⟨da⟩ := a.property
  have hleft := pair_right_bind (R := R) (inputSplit A) (zeroUnitDeriv A (⊥ : ε)) da
  have hright := pair_then_left_any (R := R) (inputSplit A)
    (zeroUnitDeriv A (⊤ : ε)) (identityDeriv A (⊤ : ε)) da
  have hid := Equates.pair (inputSplit A)
    (Equates.refl (R := R) ⟨zeroUnitDeriv A (⊤ : ε)⟩) (identity_compose_equates R a)
  simp only [composeArrow, composeTerm, identityArrow, continuation_atIndex] at hid
  simpa only [composeArrow, composeTerm, leftUnitInvArrow, leftArrow,
    continuation_atIndex, atIndex, Tm.lift, Tm.rename] using hleft.symm.trans (hright.trans hid).symm

theorem rightUnitInv_natural (hR : R.RenamingClosed) {A B : τ}
    (a : Hom (ε := ε) F R A B) :
    compose hR a (rightUnitInv B) =
      compose hR (rightUnitInv A) (right hR a Silmaril.unit) := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (rightUnitInv_natural_equates a)

theorem leftUnitInv_natural (hR : R.RenamingClosed) {A B : τ}
    (a : Hom (ε := ε) F R A B) :
    compose hR a (leftUnitInv B) =
      compose hR (leftUnitInv A) (left hR Silmaril.unit a) := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (leftUnitInv_natural_equates a)

/-- The right unitor is natural for every effect. -/
theorem rightUnit_natural (hR : R.RenamingClosed) {A B : τ}
    (a : Hom (ε := ε) F R A B) :
    compose hR (right hR a Silmaril.unit) (rightUnit B) =
      compose hR (rightUnit A) a := by
  have h := congrArg (fun f => compose hR f (rightUnit B))
    (rightUnitInv_natural hR a)
  simp only [compose_assoc, rightUnitInv_rightUnit, compose_identity] at h
  have h' := congrArg (compose hR (rightUnit A)) h
  rw [← compose_assoc, rightUnit_rightUnitInv, identity_compose] at h'
  exact h'.symm

/-- The left unitor is natural for every effect. -/
theorem leftUnit_natural (hR : R.RenamingClosed) {A B : τ}
    (a : Hom (ε := ε) F R A B) :
    compose hR (left hR Silmaril.unit a) (leftUnit B) =
      compose hR (leftUnit A) a := by
  have h := congrArg (fun f => compose hR f (leftUnit B))
    (leftUnitInv_natural hR a)
  simp only [compose_assoc, leftUnitInv_leftUnit, compose_identity] at h
  have h' := congrArg (compose hR (leftUnit A)) h
  rw [← compose_assoc, leftUnit_leftUnitInv, identity_compose] at h'
  exact h'.symm

/-- Swapping a computed pair can move its pure first component past the
second computation. The quantitative beta bound is retained explicitly. -/
theorem pair_then_swap {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a b : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γl (⊥ : ε) a A) (hb : HasType F Γr (⊤ : ε) b B)
    (hq : quantity A ≤ Γl.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair a b) (atIndex 0 (swapArrow (F := F) (Φ := Φ) (ε := ε) A B).val))
      (.pair b a) (product B A) := by
  have hp := HasType.pair s ha.top hb
  have hbody := swapParametersDeriv (F := F) (Φ := Φ) Γ.zero Γ.zero_discardable A B (⊤ : ε)
  have hmid := HasType.let₂ (QCtx.Split.zero_left Γ) hp hbody
  have hbind := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBind (QCtx.Split.zero_left Γ) hp hbody) ⟨hmid⟩
    (show WellTyped (ε := ε) F Γ
      (.let₁ (.pair a b) (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1)))) (product B A) from
      ⟨.let₁ (QCtx.Split.zero_left Γ) hp (atZeroDeriv Γ (swapDeriv A B (⊤ : ε)))⟩)
  have hbLift := hb.rename Fin.succ (.insertZero Γr A)
  rw [show Tm.rename Fin.succ b = b.lift from rfl] at hbLift
  have hseq := HasType.let₁ ((QCtx.Split.zero_left Γr).snoc (.left (.used ⊤)))
    hbLift (swapParametersDeriv Γr.zero Γr.zero_discardable A B (⊤ : ε))
  have hbeta := Equates.ofAxiom (R := R)
    (EquationAxiom.pairBeta (QCtx.Split.zero_right Γ) s ha.top hb hbody)
    ⟨hmid⟩ ⟨.let₁ s.symm ha.top hseq⟩
  have hpost := pair_left_bind_any (R := R) s.symm hb ha.top
  have he : Tm.instantiate (.let₁ b.lift (.pair (.bv 0) (.bv 1))) a =
      .let₁ b (.pair (.bv 0) a.lift) := by
    change Tm.let₁ (Tm.instantiate b.lift a) (.pair (.bv 0) a.lift) = _
    rw [instantiate_lift]
  have hsubst := pureBeta (R := R) s ha hseq hq
    (by rw [he]; exact hpost.1.wellTyped.2)
  have hbind' : Equates (ε := ε) F R Γ
      (.let₂ (.pair a b) (.pair (.bv 0) (.bv 1)))
      (.let₁ (.pair a b) (atIndex 0 (swapArrow (F := F) (Φ := Φ) (ε := ε) A B).val))
      (product B A) := hbind
  exact ((hbind'.symm.trans hbeta).trans (by simpa only [he] using hsubst)).trans hpost.symm

/-- The symmetry commutes with a computation on its second component. -/
theorem swap_left_natural_equates (hR : R.RenamingClosed) (A : τ) {B C : τ}
    (a : Arrow (Φ := Φ) (ε := ε) F B C) :
    Equates (ε := ε) F R (input (product A B))
      (composeArrow (leftArrow A a) (swapArrow A C)).val
      (composeArrow (swapArrow A B) (rightArrow a A)).val (product C A) := by
  obtain ⟨da⟩ := a.property
  let P := product A B
  have dar : HasType F (pairRightContext P A B) (⊤ : ε) (onRight a.val) C :=
    da.rename _ (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have hq : quantity A ≤ (pairLeftContext P A B).linearity := by
    simp only [pairLeftContext, QCtx.linearity_snoc, Usage.linearity_zero,
      Usage.linearity_used, QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_rfl le_top)
  have hl := pair_then_swap (R := R) (pairSplit P A B) (leftParameter P A B (⊥ : ε)) dar hq
  have hr := pair_then_right (R := R) (pairSplit P A B).symm
    (rightParameter P A B (⊤ : ε)) (leftParameter P A B (⊥ : ε)) da hq
  have hid := singleton_identity (R := R) hR a _
    (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl :
      QCtx.Weakening (pairRightContext P A B) (input B)
        (Tm.up (fun i : Fin 0 => i.succ.succ)))
  have hr' := hr.trans (Equates.pair (pairSplit P A B).symm hid
    (Equates.refl (R := R) ⟨leftParameter P A B (⊤ : ε)⟩))
  have hbody := hl.trans hr'.symm
  have houter := Equates.let₂ (inputSplit P)
    (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hbody
  have hfirst := destruct_compose (R := R)
    (HasType.pair (pairSplit P A B) (leftParameter P A B (⊤ : ε)) dar)
    (swapDeriv A C (⊤ : ε))
  have hlast := destruct_compose (R := R)
    (HasType.pair (pairSplit P A B).symm (rightParameter P A B (⊤ : ε))
      (leftParameter P A B (⊤ : ε))) (rightDeriv A da)
  exact (hfirst.trans houter).trans hlast.symm

theorem swap_left_natural (hR : R.RenamingClosed) (A : τ) {B C : τ}
    (a : Hom (ε := ε) F R B C) :
    compose hR (left hR A a) (swap A C) =
      compose hR (swap A B) (right hR a A) := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (swap_left_natural_equates hR A a)

/-- Naturality in the other component follows from involutivity. -/
theorem swap_right_natural (hR : R.RenamingClosed) {A B : τ}
    (a : Hom (ε := ε) F R A B) (C : τ) :
    compose hR (right hR a C) (swap B C) =
      compose hR (swap A C) (left hR C a) := by
  have h := congrArg (fun f => compose hR f (swap B C)) (swap_left_natural hR C a)
  simp only [compose_assoc, swap_swap, compose_identity] at h
  have h' := congrArg (compose hR (swap A C)) h
  rw [← compose_assoc, swap_swap, identity_compose] at h'
  exact h'.symm

end Silmaril.Isotope.Refinement.Models.Syntactic
