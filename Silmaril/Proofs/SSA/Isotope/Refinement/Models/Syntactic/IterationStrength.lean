module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterationUniformity

/-! # Strength for native iteration with a retained linear environment -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem distributorInv_action {n : Nat} {Γ Γa Γs : QCtx τ n}
    {a s : Term Φ n} {A B C : τ} (cap : F.HasCase) (split : Γ.Split Γa Γs)
    (ha : HasType F Γa (⊥ : ε) a A) (hs : HasType F Γs (⊤ : ε) s (coprod B C))
    (hqa : quantity A ≤ Γa.linearity) :
    Equates (ε := ε) F R Γ (action (.pair a s) distributorInvTerm)
      (.case s (.inl (.pair a.lift (.bv 0))) (.inr (.pair a.lift (.bv 0))))
      (coprod (product A B) (product A C)) := by
  have hlin (E : τ) : Usage.effective (.used .linear) (quantity E) ≤
      Usage.effective (.used ⊤) (quantity E) := by
    change Quantity.linear ⊓ quantity E ≤ ⊤ ⊓ quantity E
    exact inf_le_inf bot_le le_rfl
  have dl := HasType.inl (B := C) cap (zeroParameter (Φ := Φ) Γs B (.used ⊤) (⊤ : ε) (hlin B))
  have dr := HasType.inr (A := B) cap (zeroParameter (Φ := Φ) Γs C (.used ⊤) (⊤ : ε) (hlin C))
  have heta := Equates.ofAxiom (R := R) (.caseEta cap hs)
    ⟨.case cap (QCtx.Split.zero_left Γs) hs dl dr⟩ ⟨hs⟩
  have hpair := Equates.pair split (Equates.refl ⟨ha.top⟩) heta.symm
  have hmove := pair_case_right (R := R) cap split.symm (QCtx.Split.zero_left Γs) hs dl dr ha
  have hk := distributorInvDeriv (Φ := Φ) cap A B C (⊤ : ε)
  apply (action_congr hpair hk).trans
  apply (action_congr hmove hk).trans
  apply (action_case cap split hs (pairInlBindDeriv cap ha B C).top
    (pairInrBindDeriv cap ha B C).top hk).trans
  have qlift (E : τ) : quantity A ≤ (Γa.snoc E .zero).linearity := by
    rw [QCtx.linearity_snoc, Usage.linearity_zero]
    exact le_inf le_top hqa
  have qparam (E : τ) : quantity E ≤ (Γa.zero.snoc E).linearity := by
    rw [QCtx.linearity_snoc, Usage.linearity_used, QCtx.zero_linearity]
    exact le_inf (le_inf le_rfl le_top) le_top
  apply Equates.case cap split (Equates.refl ⟨hs⟩)
  · exact distributorInv_inl_action cap
      ((QCtx.Split.zero_right Γa).snoc (.right (.used ⊤)))
      (ha.rename Fin.succ (.insertZero Γa B))
      (zeroParameter Γa B (.used ⊤) (⊥ : ε) (hlin B)) (qlift B) (qparam B)
  · exact distributorInv_inr_action cap
      ((QCtx.Split.zero_right Γa).snoc (.right (.used ⊤)))
      (ha.rename Fin.succ (.insertZero Γa C))
      (zeroParameter Γa C (.used ⊤) (⊥ : ε) (hlin C)) (qlift C) (qparam C)

def iterationStepTerm (f : Term Φ 1) : Term Φ 1 :=
  composeTerm (leftTerm f) distributorInvTerm

def iterationStepDeriv (cap : F.HasCase) (D : τ) {A B : τ} {e : ε}
    {f : Term Φ 1} (hf : HasType F (input A) e f (coprod B A)) :
    HasType F (input (product D A)) e (iterationStepTerm f)
      (coprod (product D B) (product D A)) :=
  composeDeriv (leftDeriv D hf) (distributorInvDeriv cap D B A e)

theorem iterationStep_action {n : Nat} {Γ Γa Γb : QCtx τ n}
    {a b : Term Φ n} {f : Term Φ 1} {D A B : τ} (cap : F.HasCase)
    (split : Γ.Split Γa Γb) (ha : HasType F Γa (⊥ : ε) a D)
    (hb : HasType F Γb (⊤ : ε) b A) (hf : HasType F (input A) (⊤ : ε) f (coprod B A))
    (hqa : quantity D ≤ Γa.linearity) :
    Equates (ε := ε) F R Γ (action (.pair a b) (iterationStepTerm f))
      (.case (action b f) (.inl (.pair a.lift (.bv 0))) (.inr (.pair a.lift (.bv 0))))
      (coprod (product D B) (product D A)) :=
  (action_compose (HasType.pair split ha.top hb) (leftDeriv D hf)
    (distributorInvDeriv cap D B A (⊤ : ε))).trans
    ((action_congr (pair_then_left split ha hb hf hqa)
      (distributorInvDeriv cap D B A (⊤ : ε))).trans
      (distributorInv_action cap split ha (actionDeriv hb hf) hqa))


theorem atZero_equates (hR : R.RenamingClosed) {n : Nat} (Γ : QCtx τ n)
    {a b : Term Φ 1} {A B : τ} (h : Equates (ε := ε) F R (input A) a b B) :
    Equates (ε := ε) F R (Γ.zero.snoc A) (atIndex 0 a) (atIndex 0 b) B := by
  have hw := (QCtx.discardable_iff_weakening_nil.mp (QCtx.zero_discardable Γ)).up A
  have he := h.rename _ hw hR
  convert he using 1 <;> apply Tm.rename_congr <;> intro i <;>
    have hi : i = 0 := Fin.eq_zero i <;> subst i <;> rfl

theorem zero_action_equates (hR : R.RenamingClosed) {n : Nat} (Γ : QCtx τ n)
    {f : Term Φ 1} {A B : τ} (hf : HasType F (input A) (⊤ : ε) f B) :
    Equates (ε := ε) F R (Γ.zero.snoc A) (action (.bv 0) f) (atIndex 0 f) B := by
  have h := atZero_equates hR Γ
    (identity_compose_equates R (⟨f, ⟨hf⟩⟩ : Arrow (ε := ε) F A B))
  change Equates (ε := ε) F R (Γ.zero.snoc A)
    (atIndex 0 (composeTerm (.bv 0) f)) (atIndex 0 f) B at h
  rw [atIndex_compose] at h
  simpa only [action, atIndex, Tm.rename] using h

/-- The environment is retained by the uniformity rule, so no copy or discard
bound is imposed on it. -/
theorem iterate_strength_action (hR : R.RenamingClosed) {n : Nat}
    {Γ Γa Γb : QCtx τ n} {a b : Term Φ n} {f : Term Φ 1} {D A B : τ}
    (cap : F.HasIter) (split : Γ.Split Γa Γb)
    (ha : HasType F Γa (⊥ : ε) a D) (hb : HasType F Γb (⊥ : ε) b A)
    (hf : HasType F (input A) (⊤ : ε) f (coprod B A))
    (hqa : quantity D ≤ Γa.linearity) (hqb : quantity A ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a b) (iterateTerm (iterationStepTerm f)))
      (.pair a (action b (iterateTerm f))) (product D B) := by
  let cc := iter_hasCase cap
  have hlin (E : τ) : Usage.effective (.used .linear) (quantity E) ≤
      Usage.effective (.used ⊤) (quantity E) := by
    change Quantity.linear ⊓ quantity E ≤ ⊤ ⊓ quantity E
    exact inf_le_inf bot_le le_rfl
  have da := ha.rename Fin.succ (.insertZero Γa A)
  have db := zeroParameter (F := F) (Φ := Φ) Γa A (.used ⊤) (⊥ : ε) (hlin A)
  have sa := (QCtx.Split.zero_right Γa).snoc (A := A) (.right (.used ⊤))
  have qa : quantity D ≤ (Γa.snoc A .zero).linearity := by
    rw [QCtx.linearity_snoc, Usage.linearity_zero]
    exact le_inf le_top hqa
  have hstep := iterationStep_action (R := R) cc sa da db.top hf qa
  have hid := zero_action_equates (R := R) hR Γa hf
  have hc := Equates.case cc sa hid
    (Equates.refl (R := R) ⟨(HasType.inl cc
      (pairRightBindDeriv da B (.used ⊤) (hlin B))).top⟩)
    (Equates.refl (R := R) ⟨(HasType.inr cc
      (pairRightBindDeriv da A (.used ⊤) (hlin A))).top⟩)
  have hsq := hstep.trans hc
  have dstep := iterationStepDeriv cc D hf
  have ds := pairRightBindDeriv ha A (.used ⊤) (hlin A)
  have dc := pairRightBindDeriv ha B (.used ⊤) (hlin B)
  have dl : HasType F (Γa.snoc A) (⊤ : ε)
      (.iter (.pair a.lift (.bv 0)) (atIndex 0 (iterationStepTerm f))) (product D B) :=
    .iter cap (QCtx.Split.zero_left _) (Γa.snoc A).zero_linearity EffectSystem.iterable_top
      ds.top (atZeroDeriv (Γa.snoc A) dstep)
  have hleft := pureBetaTyped (R := R) split.symm hb dl hqb
  have hle : Equates (ε := ε) F R Γ
      (.let₁ b (.iter (.pair a.lift (.bv 0)) (atIndex 0 (iterationStepTerm f))))
      (.iter (.pair a b) (atIndex 0 (iterationStepTerm f))) (product D B) := by
    convert hleft using 1
    change Tm.iter (.pair a b) (atIndex 0 (iterationStepTerm f)) =
      .iter (.pair (Tm.instantiate a.lift b) b)
        (Tm.bsubst (Tm.upSub (Fin.cases b Tm.bv)) (atIndex 0 (iterationStepTerm f)))
    rw [instantiate_lift]
    congr 1
    simp only [atIndex, Tm.bsubst_rename, Tm.upSub, Fin.cases_zero, Tm.bsubst_bv_eq_rename]
  have dr : HasType F Γb (⊤ : ε) (.iter b (atIndex 0 f)) B :=
    .iter cap (QCtx.Split.zero_left _) Γb.zero_linearity EffectSystem.iterable_top hb.top
      (atZeroDeriv Γb hf)
  have hre := pair_right_bind (R := R) split ha dr
  have hr : Equates (ε := ε) F R Γ
      (.let₁ (.iter b (atIndex 0 f)) (.pair a.lift (.bv 0)))
      (.pair a (action b (iterateTerm f))) (product D B) :=
    hre.symm.trans (Equates.pair split (Equates.refl ⟨ha.top⟩)
      (action_iterate cap hb.top hf).symm)
  have heq : Equates (ε := ε) F R Γ
      (.let₁ b (.iter (.pair a.lift (.bv 0)) (atIndex 0 (iterationStepTerm f))))
      (.let₁ (.iter b (atIndex 0 f)) (.pair a.lift (.bv 0))) (product D B) := by
    have law (p : Polarity) := UniformityRule.square (ε := ε) (p := p) cap split
      (QCtx.Split.zero_left Γa) Γa.zero_linearity EffectSystem.iterable_top hb.top ds
      (atZeroDeriv Γa dstep) (atZeroDeriv Γa hf) dc.top (EffectSystem.pure_moves p ⊤)
    have hsq' : Equates (ε := ε) F R (Γa.snoc A)
        (.let₁ (.pair a.lift (.bv 0)) (atIndex 0 (iterationStepTerm f)))
        (.case (atIndex 0 f) (.inl (.pair a.lift.lift (.bv 0)))
          (.inr (.pair a.lift.lift (.bv 0)))) (coprod (product D B) (product D A)) := hsq
    have hright : WellTyped (ε := ε) F Γ
        (.let₁ (.iter b (atIndex 0 f)) (.pair a.lift (.bv 0))) (product D B) :=
      ⟨.let₁ split dr dc.top⟩
    have hp : (Tm.pair a.lift (.bv 0)).underBinder = .pair a.lift.lift (.bv 0) := by
      change Tm.pair (Tm.rename (Tm.up Fin.succ) a.lift) (.bv 0) = _
      rw [Tm.rename_lift]
      rfl
    have hn (p : Polarity) := Refines.uniformity (R := R) p (law p)
      (by simpa only [underBinder_atIndex_zero] using hle.1.wellTyped.1)
      hright
      (by cases p with
          | positive => simpa only [hp, underBinder_atIndex_zero, Polarity.source,
              Polarity.target, Polarity.orient] using hsq'.1
          | negative => simpa only [hp, underBinder_atIndex_zero, Polarity.source,
              Polarity.target, Polarity.orient] using hsq'.2)
    constructor
    · simpa only [underBinder_atIndex_zero, Polarity.source, Polarity.target,
        Polarity.orient] using hn .positive
    · simpa only [underBinder_atIndex_zero, Polarity.source, Polarity.target,
        Polarity.orient] using hn .negative
  exact (action_iterate cap (HasType.pair split ha hb).top dstep).trans
    (hle.symm.trans (heq.trans hr))


theorem iterate_strength (hR : R.RenamingClosed) (cap : F.HasIter) (D : τ) {A B : τ}
    (f : Hom (ε := ε) F R A (coprod B A)) :
    iterate hR cap (compose hR (left hR D f) (distributorInv (iter_hasCase cap) D B A)) =
      left hR D (iterate hR cap f) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    obtain ⟨hf⟩ := f.property
    apply Quotient.sound
    change Equates (ε := ε) F R (input (product D A))
      (iterateTerm (iterationStepTerm f.val)) (leftTerm (iterateTerm f.val)) (product D B)
    apply pair_ext
      (iterateDeriv cap EffectSystem.iterable_top (iterationStepDeriv (iter_hasCase cap) D hf))
      (leftDeriv D (iterateDeriv cap EffectSystem.iterable_top hf))
    exact (iterate_strength_action hR cap (pairSplit (product D A) D A)
      (leftParameter _ _ _ (⊥ : ε)) (rightParameter _ _ _ (⊥ : ε)) hf
      (leftParameter_quantity _ _ _) (rightParameter_quantity _ _ _)).trans
      (pair_then_left (pairSplit (product D A) D A)
        (leftParameter _ _ _ (⊥ : ε)) (rightParameter _ _ _ (⊤ : ε))
        (iterateDeriv cap EffectSystem.iterable_top hf) (leftParameter_quantity _ _ _)).symm

end Silmaril.Isotope.Refinement.Models.Syntactic
