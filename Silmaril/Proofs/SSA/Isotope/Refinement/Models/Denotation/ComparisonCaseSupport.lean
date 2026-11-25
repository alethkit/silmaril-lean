module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonCase
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonSupport

/-! # Common branch supports for case comparison

Both branches retain the union of their ambient supports. Keeping the newest
bound slot makes this restriction independent of its hidden summand type.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace HasType
variable {F : Fragment} {n : Nat} {Γ : QCtx (Ty α) n} {e : ε}

/-- Restrict an ambient binder context to any covering mask, retaining its bound slot. -/
def outerRestrict₁ {a : Term Φ (n+1)} {A B : Ty α} (h : HasType F (Γ.snoc A) e a B)
    (p : Fin n → Bool) (hp : ∀ i, Term.uses a i.succ = true → p i = true) :
    HasType F ((Γ.restrict p).snoc A) e a B :=
  (h.restrict (Fin.cases true p)
    (fun i => Fin.cases (fun _ => rfl) hp i)).castContext (QCtx.restrict_snoc_true _ _ _ _)

/-- Slots outside a covering mask can be discarded. -/
theorem outerRestrictWeakening₁ {a : Term Φ (n+1)} {A B : Ty α} (h : HasType F (Γ.snoc A) e a B)
    (p : Fin n → Bool) (hp : ∀ i, Term.uses a i.succ = true → p i = true) :
    QCtx.Weakening Γ (Γ.restrict p) id := by
  apply QCtx.weakening_restrict
  intro i hi
  apply (h.slotAllows i.succ).2
  cases hx : Term.uses a i.succ
  · rfl
  · exact False.elim (Bool.noConfusion (hi.symm.trans (hp i hx)))

/-- Branches sharing an ambient context allow the union of their supports. -/
theorem caseOuterAllows {l r : Term Φ (n+1)} {A B C : Ty α}
    (hl : HasType F (Γ.snoc A) e l C) (hr : HasType F (Γ.snoc B) e r C) (i : Fin n) :
    QCtx.SlotAllows (Γ i).1 (Γ i).2 (Term.uses l i.succ || Term.uses r i.succ) :=
  (hl.slotAllows i.succ).or (hr.slotAllows i.succ)

/-- Left and right branch contexts from independent typings align on the same union mask. -/
theorem caseOuter_aligned {Δ : QCtx (Ty α) n} {e' : ε} {l r : Term Φ (n+1)} {A B C D E G : Ty α}
    (hl : HasType F (Γ.snoc A) e l E) (hr : HasType F (Γ.snoc B) e r E)
    (kl : HasType F (Δ.snoc C) e' l G) (kr : HasType F (Δ.snoc D) e' r G) :
    QCtx.Aligned (Γ.restrict (fun i => Term.uses l i.succ || Term.uses r i.succ))
      (Δ.restrict (fun i => Term.uses l i.succ || Term.uses r i.succ)) :=
  QCtx.Aligned.restrict_of_nonzero Γ Δ _ (fun i => (hl.caseOuterAllows hr i).1)
    (fun i => (kl.caseOuterAllows kr i).1)
end HasType

namespace Models.Denotation
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K)
include N

/-- Restricting a binder's ambient support is interpreted by environment weakening. -/
theorem denote_outerRestrict₁ {n : Nat} {Γ : QCtx (Ty α) n} {e : ε}
    {a : Term Φ (n+1)} {A B : Ty α} (h : HasType F (Γ.snoc A) e a B)
    (p : Fin n → Bool) (hp : ∀ i, Term.uses a i.succ = true → p i = true) :
    denote M.toSeqData K h = M.compose (M.right (weaken M.toSeqData (h.outerRestrictWeakening₁ p hp)) A)
      (denote M.toSeqData K (h.outerRestrict₁ p hp)) := by
  rw [denote_restrict_to M.toSeqModel K N h (Fin.cases true p)
    (fun i => Fin.cases (fun _ => rfl) hp i) (QCtx.restrict_snoc_true _ _ _ _)
    ((h.outerRestrictWeakening₁ p hp).keepNewest A), weaken_snoc M.toSeqModel A (h.outerRestrictWeakening₁ p hp)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A case typing factors through the argument support and the union of branch supports. -/
theorem denote_case_support {n : Nat} {Γ Γl Γr : QCtx (Ty α) n} {e : ε}
    {a : Term Φ n} {l r : Term Φ (n+1)} {A B C : Ty α}
    (cap : F.HasCase) (s : QCtx.Split Γ Γl Γr) (ha : HasType F Γr e a (coprod A B))
    (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C) :
    denote M.toSeqData K (.case cap s ha hl hr) =
      M.compose (weaken M.toSeqData (s.supportWeakening
        (fun i => Term.uses l i.succ || Term.uses r i.succ) (Term.uses a) (hl.caseOuterAllows hr) ha.slotAllows))
        (denote M.toSeqData K (.case cap (s.restrictOutputs
          (fun i => Term.uses l i.succ || Term.uses r i.succ) (Term.uses a)
          (fun i => (hl.caseOuterAllows hr i).1) (fun _ => ha.used_nonzero)) ha.support
            (hl.outerRestrict₁ _ (fun _ h => Bool.or_eq_true_iff.mpr (.inl h)))
            (hr.outerRestrict₁ _ (fun _ h => Bool.or_eq_true_iff.mpr (.inr h))))) := by
  let p := fun i : Fin n => Term.uses l i.succ || Term.uses r i.succ
  let q := Term.uses a
  let w := s.supportWeakening p q (hl.caseOuterAllows hr) ha.slotAllows
  let sc := s.restrictOutputs p q (fun i => (hl.caseOuterAllows hr i).1) (fun _ => ha.used_nonzero)
  let pl : ∀ i, Term.uses l i.succ = true → p i = true := fun _ h => Bool.or_eq_true_iff.mpr (.inl h)
  let pr : ∀ i, Term.uses r i.succ = true → p i = true := fun _ h => Bool.or_eq_true_iff.mpr (.inr h)
  let wl := hl.outerRestrictWeakening₁ p pl
  let wr := ha.supportWeakening
  change M.compose (split M.toSeqData s)
    (M.compose (M.left _ (denote M.toSeqData K ha))
      (M.compose (K.distribute cap _ A B) (K.desc cap (denote M.toSeqData K hl) (denote M.toSeqData K hr)))) =
    M.compose (weaken M.toSeqData w) (M.compose (split M.toSeqData sc)
      (M.compose (M.left _ (denote M.toSeqData K ha.support))
        (M.compose (K.distribute cap _ A B)
          (K.desc cap (denote M.toSeqData K (hl.outerRestrict₁ p pl)) (denote M.toSeqData K (hr.outerRestrict₁ p pr))))))
  rw [denote_restrict M.toSeqModel K N ha _ (fun _ => id),
    denote_outerRestrict₁ M K N hl p pl, denote_outerRestrict₁ M K N hr p pr,
    ← N.case_natural, ← M.compose_assoc (M.left _ _) (M.right _ _),
    ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl)]
  simp only [← M.compose_assoc]
  exact congrArg (fun f => M.compose (M.compose (M.compose f
      (M.left (packed (Γl.restrict p)) (denote M.toSeqData K ha.support)))
        (K.distribute cap (packed (Γl.restrict p)) A B))
          (K.desc cap (denote M.toSeqData K (hl.outerRestrict₁ p pl)) (denote M.toSeqData K (hr.outerRestrict₁ p pr))))
    (weaken_split M.toSeqModel w s sc wl wr).symm

omit N in
set_option backward.isDefEq.respectTransparency false in
/-- Case comparison is independent of the original resource-allocation witnesses. -/
theorem TypingComparison.case_support [DecidableEq α]
    (it : F.HasIter → ∀ {A B : Ty α}, M.Hom A (coprod B A) → M.Hom A B)
    (N : ControlEnvironment (ControlData.ofCase M F it))
    {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {l r : Term Φ (n+1)} {A B C D E G : Ty α}
    (cap : F.HasCase) (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hc : QCtx.Aligned Γ Δ)
    (ha : HasType F Γr e a (coprod A B)) (ka : HasType F Δr e' a (coprod C D))
    (hb : HasType F (Γl.snoc A) e l E) (kb : HasType F (Δl.snoc C) e' l G)
    (hd : HasType F (Γl.snoc B) e r E) (kd : HasType F (Δl.snoc D) e' r G)
    (ca : TypingComparison M (ControlData.ofCase M F it) ha.support ka.support (ha.support_aligned ka))
    (cb : TypingComparison M (ControlData.ofCase M F it)
      (hb.outerRestrict₁ (fun i => Term.uses l i.succ || Term.uses r i.succ) (fun _ h => Bool.or_eq_true_iff.mpr (.inl h)))
      (kb.outerRestrict₁ (fun i => Term.uses l i.succ || Term.uses r i.succ) (fun _ h => Bool.or_eq_true_iff.mpr (.inl h)))
      ((hb.caseOuter_aligned hd kb kd).snoc A C))
    (cd : TypingComparison M (ControlData.ofCase M F it)
      (hd.outerRestrict₁ (fun i => Term.uses l i.succ || Term.uses r i.succ) (fun _ h => Bool.or_eq_true_iff.mpr (.inr h)))
      (kd.outerRestrict₁ (fun i => Term.uses l i.succ || Term.uses r i.succ) (fun _ h => Bool.or_eq_true_iff.mpr (.inr h)))
      ((hb.caseOuter_aligned hd kb kd).snoc B D)) :
    TypingComparison M (ControlData.ofCase M F it) (.case cap s ha hb hd) (.case cap t ka kb kd) hc := by
  let p := fun i : Fin n => Term.uses l i.succ || Term.uses r i.succ
  let q := Term.uses a
  let pl : ∀ i, Term.uses l i.succ = true → p i = true := fun _ h => Bool.or_eq_true_iff.mpr (.inl h)
  let pr : ∀ i, Term.uses r i.succ = true → p i = true := fun _ h => Bool.or_eq_true_iff.mpr (.inr h)
  let sc := s.restrictOutputs p q (fun i => (hb.caseOuterAllows hd i).1) (fun _ => ha.used_nonzero)
  let tc := t.restrictOutputs p q (fun i => (kb.caseOuterAllows kd i).1) (fun _ => ka.used_nonzero)
  let w := s.supportWeakening p q (hb.caseOuterAllows hd) ha.slotAllows
  let v := t.supportWeakening p q (kb.caseOuterAllows kd) ka.slotAllows
  let hl := hb.caseOuter_aligned hd kb kd
  exact TypingComparison.of_factors M (ControlData.ofCase M F it) N
    (.case cap s ha hb hd) (.case cap t ka kb kd)
    (.case cap sc ha.support (hb.outerRestrict₁ p pl) (hd.outerRestrict₁ p pr))
    (.case cap tc ka.support (kb.outerRestrict₁ p pl) (kd.outerRestrict₁ p pr))
    w v (QCtx.weakening_merge_of_restrict w v) hc (hc.restrict (fun i => p i || q i))
    (denote_case_support M (ControlData.ofCase M F it) N cap s ha hb hd)
    (denote_case_support M (ControlData.ofCase M F it) N cap t ka kb kd)
    (TypingComparison.case M it cap sc tc (hc.restrict (fun i => p i || q i)) hl (ha.support_aligned ka)
      (hl.snoc A C) (hl.snoc B D) ha.support ka.support
      (hb.outerRestrict₁ p pl) (kb.outerRestrict₁ p pl) (hd.outerRestrict₁ p pr) (kd.outerRestrict₁ p pr)
      ca cb cd)

end Models.Denotation
end Silmaril.Isotope.Refinement
