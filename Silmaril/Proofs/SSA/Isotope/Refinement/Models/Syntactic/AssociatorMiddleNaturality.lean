module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorLeftNaturality

/-! # Naturality of reassociation in its middle component -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Reassociation also preserves an effectful middle leaf. -/
theorem assoc_pair_middle {n : Nat} {Γ Γab Γa Γb Γc : QCtx τ n}
    {a b c : Term Φ n} {A B C : τ}
    (s : Γ.Split Γab Γc) (t : Γab.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a A) (hb : HasType F Γb (⊤ : ε) b B)
    (hc : HasType F Γc (⊥ : ε) c C)
    (hqa : quantity A ≤ Γa.linearity) (hqc : quantity C ≤ Γc.linearity) :
    Equates (ε := ε) F R Γ
      (.let₁ (.pair (.pair a b) c) (atIndex 0 (assocTerm (Φ := Φ))))
      (.pair a (.pair b c)) (product A (product B C)) := by
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  have hd (q : Usage) (hq : Usage.effective (.used .linear) (quantity B) ≤
      Usage.effective q (quantity B)) :
      HasType F ((Γc.snoc A).snoc B q) (⊥ : ε)
        (.pair (.bv 1) (.pair (.bv 0) c.lift.lift)) (product A (product B C)) :=
    .pair (((QCtx.Split.zero_left Γc).snoc (.left (.used ⊤))).snoc (.right q))
      ((zeroParameter Γc A (.used ⊤) (⊥ : ε) (hlin A)).rename Fin.succ (.insertZero _ B))
      (pairLeftBindDeriv (hc.rename Fin.succ (.insertZero Γc A)) B q hq)
  have h₁ := pair_then_assoc_right (R := R) s (HasType.pair t ha.top hb) hc hqc
  have h₂ := mixedPairBeta (R := R) s t ha hb (hd (.used .linear) le_rfl)
    (hd (.used ⊤) (hlin B)) hqa (EffectSystem.pure_commutes (⊤ : ε)).symm
  apply h₁.trans
  convert h₂ using 1
  change Tm.pair a (.pair b c) =
    .pair (Tm.instantiate a.lift b)
      (.pair b (Tm.instantiate (Tm.bsubst (Tm.upSub (Fin.cases a Tm.bv)) c.lift.lift) b))
  rw [instantiate_lift, Tm.bsubst_lift]
  change Tm.pair a (.pair b c) =
    .pair a (.pair b (Tm.instantiate (Tm.instantiate c.lift a).lift b))
  rw [instantiate_lift, instantiate_lift]

theorem assoc_natural_middle_equates (hR : R.RenamingClosed) (A : τ) {B C : τ}
    (f : Arrow (Φ := Φ) (ε := ε) F B C) (D : τ) :
    Equates (ε := ε) F R (input (product (product A B) D))
      (composeArrow (rightArrow (leftArrow A f) D) (assocArrow A C D)).val
      (composeArrow (assocArrow A B D) (leftArrow A (rightArrow f D))).val
      (product A (product C D)) := by
  obtain ⟨df⟩ := f.property
  let P := product (product A B) D
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc D .zero).snoc A).snoc B .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc D .zero).snoc A .zero).snoc B
  let Γd : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc D).snoc A .zero).snoc B .zero
  have da : HasType F Γa (⊥ : ε) (.bv 1 : Term Φ 5) A :=
    singleVariable Γa 1 ⊥ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db : HasType F Γb (⊥ : ε) (.bv 0 : Term Φ 5) B :=
    singleVariable Γb 0 ⊥ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dd : HasType F Γd (⊥ : ε) (.bv 2 : Term Φ 5) D :=
    singleVariable Γd 2 ⊥ rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have hw : QCtx.Weakening Γb (input B) (Tm.up (fun j : Fin 0 => j.succ.succ.succ.succ)) :=
    .cons (.skip (.skip (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl
  have hw' : QCtx.Weakening Γb (input B) (fun _ => (0 : Fin 5)) := by
    convert hw using 1
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  have dfb : HasType F Γb (⊤ : ε) (atIndex 0 f.val) C := df.rename _ hw'
  have sbd := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A B) (.left .zero)).snoc
    (A := D) (.right (.used ⊤))).snoc (A := A) (.left .zero)).snoc (A := B) (.left (.used ⊤)))
  have sabd := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A B) (.left .zero)).snoc
    (A := D) (.right (.used ⊤))).snoc (A := A) (.left (.used ⊤))).snoc (A := B) (.right (.used ⊤)))
  have sab := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A B) (.left .zero)).snoc
    (A := D) (.left .zero)).snoc (A := A) (.left (.used ⊤))).snoc (A := B) (.right (.used ⊤)))
  have sab_d := (((((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := product A B) (.left .zero)).snoc
    (A := D) (.right (.used ⊤))).snoc (A := A) (.left (.used ⊤))).snoc (A := B) (.left (.used ⊤)))
  have hqa : quantity A ≤ Γa.linearity := by
    simp only [Γa, QCtx.linearity_snoc, Usage.linearity_zero, Usage.linearity_used,
      QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_rfl (le_inf le_top (le_inf le_top le_top)))
  have hqd : quantity D ≤ Γd.linearity := by
    simp only [Γd, QCtx.linearity_snoc, Usage.linearity_zero, Usage.linearity_used,
      QCtx.linearity_nil, inf_top_eq]
    exact le_inf le_top (le_inf le_top (le_inf le_rfl (le_inf le_top le_top)))
  have hi := singleton_identity (R := R) hR f _ hw'
  have hrPair := (pair_then_right (R := R) sbd db.top dd df hqd).trans
    (Equates.pair sbd hi (Equates.refl (R := R) ⟨dd.top⟩))
  have hrTriple := (pair_then_left_any (R := R) sabd da.top (.pair sbd db.top dd.top)
    (rightDeriv D df)).trans (Equates.pair sabd (Equates.refl (R := R) ⟨da.top⟩) hrPair)
  have hr := (pair_elim_then (R := R) (pairSplit P (product A B) D).symm
    (leftParameter P (product A B) D (⊤ : ε)) (HasType.pair sabd da.top (.pair sbd db.top dd.top))
    (leftDeriv A (rightDeriv D df))).trans
    (Equates.let₂ (pairSplit P (product A B) D).symm
      (Equates.refl (R := R) ⟨leftParameter P (product A B) D (⊤ : ε)⟩) hrTriple)
  have hmove := pair_let₂_left_any (R := R) (pairSplit P (product A B) D)
    (QCtx.Split.zero_left (pairLeftContext P (product A B) D))
    (leftParameter P (product A B) D (⊤ : ε))
    (leftBodyDeriv (pairLeftContext P (product A B) D) A df)
    (rightParameter P (product A B) D (⊤ : ε))
  have hlTriple := assoc_pair_middle (R := R) sab_d sab da dfb dd hqa hqd
  have hl := (Equates.let₁ (QCtx.Split.zero_left (pairContext P (product A B) D)) hmove
    (Equates.refl (R := R) ⟨atZeroDeriv (pairContext P (product A B) D) (assocDeriv A C D (⊤ : ε))⟩)).trans
    ((pair_elim_then (R := R) (pairSplit P (product A B) D).symm
      (leftParameter P (product A B) D (⊤ : ε))
      (HasType.pair sab_d (.pair sab da.top dfb) dd.top) (assocDeriv A C D (⊤ : ε))).trans
      (Equates.let₂ (pairSplit P (product A B) D).symm
        (Equates.refl (R := R) ⟨leftParameter P (product A B) D (⊤ : ε)⟩) hlTriple))
  have hbody := hl.trans hr.symm
  have hfirst := destruct_compose (R := R)
    (HasType.pair (pairSplit P (product A B) D)
      ((leftDeriv A df).rename _ (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl))
      (rightParameter P (product A B) D (⊤ : ε))) (assocDeriv A C D (⊤ : ε))
  have hlast := destruct_compose (R := R) (assocBodyDeriv A B D (⊤ : ε)) (leftDeriv A (rightDeriv D df))
  have houter := Equates.let₂ (inputSplit P)
    (Equates.refl (R := R) ⟨identityDeriv P (⊤ : ε)⟩) hbody
  apply hfirst.trans
  apply Equates.trans _ hlast.symm
  change Equates (ε := ε) F R (input P)
    (.let₂ (.bv 0) (.let₁ (.pair (onLeft (leftTerm f.val)) (.bv 0)) (atIndex 0 assocTerm)))
    (.let₂ (.bv 0) (.let₁ assocBody (atIndex 0 (leftTerm (rightTerm f.val))))) _
  simpa only [onLeft_atIndex, atIndex_leftTerm, assocBody] using houter

theorem assoc_natural_middle (hR : R.RenamingClosed) (A : τ) {B C : τ}
    (f : Hom (ε := ε) F R B C) (D : τ) :
    compose hR (right hR (left hR A f) D) (assoc A C D) =
      compose hR (assoc A B D) (left hR A (right hR f D)) := by
  induction f using Quotient.inductionOn with
  | _ f => exact Quotient.sound (assoc_natural_middle_equates hR A f D)

end Silmaril.Isotope.Refinement.Models.Syntactic
