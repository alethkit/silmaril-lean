module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorEffects

/-! # Naturality of reassociation in its first component -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem assoc_natural_left_equates (hR : R.RenamingClosed) {A B : τ}
    (f : Arrow (Φ := Φ) (ε := ε) F A B) (C D : τ) :
    Equates (ε := ε) F R (input (product (product A C) D))
      (composeArrow (rightArrow (rightArrow f C) D) (assocArrow B C D)).val
      (composeArrow (assocArrow A C D) (rightArrow f (product C D))).val
      (product B (product C D)) := by
  obtain ⟨df⟩ := f.property
  let P := product (product A C) D
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A C) .zero).snoc D .zero).snoc A).snoc C .zero
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A C) .zero).snoc D .zero).snoc A .zero).snoc C
  let Γd : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A C) .zero).snoc D).snoc A .zero).snoc C .zero
  have da : HasType F Γa (⊥ : ε) (.bv 1 : Term Φ 5) A :=
    singleVariable Γa 1 ⊥ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc : HasType F Γc (⊥ : ε) (.bv 0 : Term Φ 5) C :=
    singleVariable Γc 0 ⊥ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dd : HasType F Γd (⊥ : ε) (.bv 2 : Term Φ 5) D :=
    singleVariable Γd 2 ⊥ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have hw : QCtx.Weakening Γa (input A) (fun i =>
      (Tm.up (fun j : Fin 0 => j.succ.succ.succ) i).succ) :=
    .skip (.cons (.skip (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl
  have hw' : QCtx.Weakening Γa (input A) (fun _ => (1 : Fin 5)) := by
    convert hw using 1
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  have dfa : HasType F Γa (⊤ : ε) (atIndex 1 f.val) B := df.rename _ hw'
  have scd := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A C) (.left .zero)).snoc
    (A := D) (.right (.used ⊤))).snoc (A := A) (.left .zero)).snoc (A := C) (.left (.used ⊤)))
  have sacd := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A C) (.left .zero)).snoc
    (A := D) (.right (.used ⊤))).snoc (A := A) (.left (.used ⊤))).snoc (A := C) (.right (.used ⊤)))
  have sac := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A C) (.left .zero)).snoc
    (A := D) (.left .zero)).snoc (A := A) (.left (.used ⊤))).snoc (A := C) (.right (.used ⊤)))
  have sac_d := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A C) (.left .zero)).snoc
    (A := D) (.right (.used ⊤))).snoc (A := A) (.left (.used ⊤))).snoc (A := C) (.left (.used ⊤)))
  have hqc : quantity C ≤ Γc.linearity := by
    simp only [Γc, QCtx.linearity_snoc, Usage.linearity_zero, Usage.linearity_used,
      QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_rfl (le_inf le_top (le_inf le_top (le_inf le_top le_top)))
  have hqd : quantity D ≤ Γd.linearity := by
    simp only [Γd, QCtx.linearity_snoc, Usage.linearity_zero, Usage.linearity_used,
      QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_top (le_inf le_rfl (le_inf le_top le_top)))
  have hqcd := scd.le_linearity
    (show quantity C ⊓ quantity D ≤ Γc.linearity from inf_le_left.trans hqc)
    (show quantity C ⊓ quantity D ≤ Γd.linearity from inf_le_right.trans hqd)
  rw [← TypeQuantity.product_quantity] at hqcd
  have hi := singleton_identity (R := R) hR f _ hw'
  have hrTriple := (pair_then_right (R := R) sacd da.top (.pair scd dc dd) df hqcd).trans
    (Equates.pair sacd hi (Equates.refl (R := R) ⟨HasType.pair scd dc.top dd.top⟩))
  have hr := (pair_elim_then (R := R) (pairSplit P (product A C) D).symm
    (leftParameter P (product A C) D (⊤ : ε)) (HasType.pair sacd da.top (.pair scd dc.top dd.top))
    (rightDeriv (product C D) df)).trans
    (Equates.let₂ (pairSplit P (product A C) D).symm
      (Equates.refl (R := R) ⟨leftParameter P (product A C) D (⊤ : ε)⟩) hrTriple)
  have hmove := pair_let₂_left_any (R := R) (pairSplit P (product A C) D)
    (QCtx.Split.zero_left (pairLeftContext P (product A C) D))
    (leftParameter P (product A C) D (⊤ : ε))
    (rightBodyDeriv (pairLeftContext P (product A C) D) df C)
    (rightParameter P (product A C) D (⊤ : ε))
  have hlTriple := assoc_pair_first (R := R) sac_d sac dfa dc dd hqc hqd
  have hl := (Equates.let₁ (QCtx.Split.zero_left (pairContext P (product A C) D)) hmove
    (Equates.refl (R := R) ⟨atZeroDeriv (pairContext P (product A C) D) (assocDeriv B C D (⊤ : ε))⟩)).trans
    ((pair_elim_then (R := R) (pairSplit P (product A C) D).symm
      (leftParameter P (product A C) D (⊤ : ε))
      (HasType.pair sac_d (.pair sac dfa dc.top) dd.top) (assocDeriv B C D (⊤ : ε))).trans
      (Equates.let₂ (pairSplit P (product A C) D).symm
        (Equates.refl (R := R) ⟨leftParameter P (product A C) D (⊤ : ε)⟩) hlTriple))
  have hbody := hl.trans hr.symm
  have hfirst := destruct_compose (R := R)
    (HasType.pair (pairSplit P (product A C) D)
      ((rightDeriv C df).rename _ (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl))
      (rightParameter P (product A C) D (⊤ : ε))) (assocDeriv B C D (⊤ : ε))
  have hlast := destruct_compose (R := R) (assocBodyDeriv A C D (⊤ : ε)) (rightDeriv (product C D) df)
  have houter := Equates.let₂ (inputSplit P)
    (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hbody
  apply hfirst.trans
  apply Equates.trans _ hlast.symm
  change Equates (ε := ε) F R (input P)
    (.let₂ (.bv 0) (.let₁ (.pair (onLeft (rightTerm f.val)) (.bv 0)) (atIndex 0 assocTerm)))
    (.let₂ (.bv 0) (.let₁ assocBody (atIndex 0 (rightTerm f.val)))) _
  simpa only [onLeft_atIndex, atIndex_rightTerm, assocBody] using houter

theorem assoc_natural_left (hR : R.RenamingClosed) {A B : τ}
    (f : Hom (ε := ε) F R A B) (C D : τ) :
    compose hR (right hR (right hR f C) D) (assoc B C D) =
      compose hR (assoc A C D) (right hR f (product C D)) := by
  induction f using Quotient.inductionOn with
  | _ f => exact Quotient.sound (assoc_natural_left_equates hR f C D)

end Silmaril.Isotope.Refinement.Models.Syntactic
