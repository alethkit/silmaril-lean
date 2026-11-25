module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Restriction
public import Silmaril.Raw.SSA.Isotope.Refinement.SupportSplitting
public import Silmaril.Raw.SSA.Isotope.Refinement.TypingCoherence

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Sequential categorical interpretation is independent of typing derivation. -/
theorem denoteSeq_coherent {n : Nat} {t : Term Φ n} {Γ : QCtx (Ty α) n} {e e' : ε} {A : Ty α}
    (h : HasType .seq Γ e t A) (k : HasType .seq Γ e' t A) : denoteSeq M h = denoteSeq M k := by
  induction t generalizing e e' A with
  | bv i => cases h; cases k; rfl
  | fv x => exact nomatch x
  | op f a ih =>
    cases h with
    | op hf ha =>
      cases k with
      | op kf ka => exact congrArg (fun a => M.toSeqData.compose a (M.instruction f)) (ih ha ka)
  | unit => cases h; cases k; rfl
  | pair a b iha ihb =>
    cases h with
    | pair s ha hb =>
      cases k with
      | pair t ka kb =>
        let hac := (ha.support).castContext (s.restrict_left_eq _ (fun i => ha.used_nonzero))
        let hbc := (hb.support).castContext (s.restrict_right_eq _ (fun i => hb.used_nonzero))
        let kac := (ka.support).castContext (t.restrict_left_eq _ (fun i => ka.used_nonzero))
        let kbc := (kb.support).castContext (t.restrict_right_eq _ (fun i => kb.used_nonzero))
        let wl := s.supportWeakening_left _ ha.slotAllows
        let wr := s.supportWeakening_right _ hb.slotAllows
        let vl := t.supportWeakening_left _ ka.slotAllows
        let vr := t.supportWeakening_right _ kb.slotAllows
        let w := s.supportWeakening _ _ ha.slotAllows hb.slotAllows
        let sc := s.support _ _ (fun i => ha.used_nonzero) (fun i => hb.used_nonzero)
        have ea : denoteSeq M ha = M.toSeqData.compose (weaken M.toSeqData wl) (denoteSeq M hac) :=
          denoteSeq_restrict_to M ha _ (fun _ => id) _ wl
        have eb : denoteSeq M hb = M.toSeqData.compose (weaken M.toSeqData wr) (denoteSeq M hbc) :=
          denoteSeq_restrict_to M hb _ (fun _ => id) _ wr
        have fa : denoteSeq M ka = M.toSeqData.compose (weaken M.toSeqData vl) (denoteSeq M kac) :=
          denoteSeq_restrict_to M ka _ (fun _ => id) _ vl
        have fb : denoteSeq M kb = M.toSeqData.compose (weaken M.toSeqData vr) (denoteSeq M kbc) :=
          denoteSeq_restrict_to M kb _ (fun _ => id) _ vr
        change M.toSeqData.compose (split M.toSeqData s)
          (M.toSeqData.tensor (denoteSeq M ha) (denoteSeq M hb)) =
          M.toSeqData.compose (split M.toSeqData t)
            (M.toSeqData.tensor (denoteSeq M ka) (denoteSeq M kb))
        rw [ea, eb, fa, fb,
          ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ wr),
          ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ vr),
          ← M.toSeqData.compose_assoc, ← M.toSeqData.compose_assoc,
          ← weaken_split M w s sc wl wr, ← weaken_split M w t sc vl vr,
          iha hac kac, ihb hbc kbc]
  | let₁ a b iha ihb =>
    cases h with
    | let₁ s ha hb =>
      rename_i S Γl Γr
      cases k with
      | let₁ t ka kb =>
        rename_i T Δl Δr
        have hA := ha.seq_result_eq ka (s.types_right.trans t.types_right.symm)
        subst T
        let pa := Term.uses a
        let pb := fun i => Term.uses b (Fin.succ i)
        have cb : Term.Covered (Fin.cases true pb) b := fun i => Fin.cases (fun _ => rfl) (fun _ => id) i
        let hac := (ha.support).castContext (s.restrict_right_eq _ (fun i => ha.used_nonzero))
        let kac := (ka.support).castContext (t.restrict_right_eq _ (fun i => ka.used_nonzero))
        have hbl := s.restrict_left_eq pb (fun i => hb.used_nonzero (i := i.succ))
        have kbl := t.restrict_left_eq pb (fun i => kb.used_nonzero (i := i.succ))
        let hbc := (hb.restrict (Fin.cases true pb) cb).castContext
          ((QCtx.restrict_snoc_true _ _ _ pb).trans (congrArg (fun G : QCtx (Ty α) _ => G.snoc S) hbl))
        let kbc := (kb.restrict (Fin.cases true pb) cb).castContext
          ((QCtx.restrict_snoc_true _ _ _ pb).trans (congrArg (fun G : QCtx (Ty α) _ => G.snoc S) kbl))
        let wl := s.supportWeakening_left pb (fun i => hb.slotAllows i.succ)
        let wr := s.supportWeakening_right pa ha.slotAllows
        let vl := t.supportWeakening_left pb (fun i => kb.slotAllows i.succ)
        let vr := t.supportWeakening_right pa ka.slotAllows
        let w := s.supportWeakening pb pa (fun i => hb.slotAllows i.succ) ha.slotAllows
        let sc := s.support pb pa (fun i => hb.used_nonzero (i := i.succ)) (fun i => ha.used_nonzero)
        have ea : denoteSeq M ha = M.toSeqData.compose (weaken M.toSeqData wr) (denoteSeq M hac) :=
          denoteSeq_restrict_to M ha _ (fun _ => id) _ wr
        have fa : denoteSeq M ka = M.toSeqData.compose (weaken M.toSeqData vr) (denoteSeq M kac) :=
          denoteSeq_restrict_to M ka _ (fun _ => id) _ vr
        have eb : denoteSeq M hb = M.toSeqData.compose (M.toSeqData.right (weaken M.toSeqData wl) S)
            (denoteSeq M hbc) := by
          rw [denoteSeq_restrict_to M hb _ cb
            ((QCtx.restrict_snoc_true _ _ _ pb).trans (congrArg (fun G => G.snoc S) hbl))
            (wl.keepNewest S), weaken_snoc M S wl]
        have fb : denoteSeq M kb = M.toSeqData.compose (M.toSeqData.right (weaken M.toSeqData vl) S)
            (denoteSeq M kbc) := by
          rw [denoteSeq_restrict_to M kb _ cb
            ((QCtx.restrict_snoc_true _ _ _ pb).trans (congrArg (fun G => G.snoc S) kbl))
            (vl.keepNewest S), weaken_snoc M S vl]
        change M.toSeqData.compose (split M.toSeqData s)
          (M.toSeqData.compose (M.toSeqData.left _ (denoteSeq M ha)) (denoteSeq M hb)) =
          M.toSeqData.compose (split M.toSeqData t)
            (M.toSeqData.compose (M.toSeqData.left _ (denoteSeq M ka)) (denoteSeq M kb))
        rw [ea, eb, fa, fb,
          ← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right (weaken M.toSeqData wl) _),
          ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl),
          ← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right (weaken M.toSeqData vl) _),
          ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ vl)]
        simp only [← M.toSeqData.compose_assoc]
        rw [← weaken_split M w s sc wl wr, ← weaken_split M w t sc vl vr,
          iha hac kac, ihb hbc kbc]
  | let₂ a b iha ihb =>
    cases h with
    | let₂ s ha hb =>
      rename_i P Q Γl Γr
      cases k with
      | let₂ t ka kb =>
        rename_i U V Δl Δr
        have hAB := ha.seq_result_eq ka (s.types_right.trans t.types_right.symm)
        obtain ⟨hA, hB⟩ := Ty.product.inj hAB
        subst U
        subst V
        let pa := Term.uses a
        let pb := fun i => Term.uses b (Fin.succ (Fin.succ i))
        have cb : Term.Covered (Fin.cases true (Fin.cases true pb)) b :=
          fun i => Fin.cases (fun _ => rfl) (fun j => Fin.cases (fun _ => rfl) (fun _ => id) j) i
        let hac := (ha.support).castContext (s.restrict_right_eq _ (fun i => ha.used_nonzero))
        let kac := (ka.support).castContext (t.restrict_right_eq _ (fun i => ka.used_nonzero))
        have hbl := s.restrict_left_eq pb (fun i => hb.used_nonzero (i := i.succ.succ))
        have kbl := t.restrict_left_eq pb (fun i => kb.used_nonzero (i := i.succ.succ))
        let hbc := (hb.restrict (Fin.cases true (Fin.cases true pb)) cb).castContext
          ((show QCtx.restrict ((Γl.snoc P).snoc Q) (Fin.cases true (Fin.cases true pb)) =
            ((QCtx.restrict Γl pb).snoc P).snoc Q by simp only [QCtx.restrict_snoc_true]).trans
            (congrArg (fun G : QCtx (Ty α) _ => (G.snoc P).snoc Q) hbl))
        let kbc := (kb.restrict (Fin.cases true (Fin.cases true pb)) cb).castContext
          ((show QCtx.restrict ((Δl.snoc P).snoc Q) (Fin.cases true (Fin.cases true pb)) =
            ((QCtx.restrict Δl pb).snoc P).snoc Q by simp only [QCtx.restrict_snoc_true]).trans
            (congrArg (fun G : QCtx (Ty α) _ => (G.snoc P).snoc Q) kbl))
        let wl := s.supportWeakening_left pb (fun i => hb.slotAllows i.succ.succ)
        let wr := s.supportWeakening_right pa ha.slotAllows
        let vl := t.supportWeakening_left pb (fun i => kb.slotAllows i.succ.succ)
        let vr := t.supportWeakening_right pa ka.slotAllows
        let w := s.supportWeakening pb pa (fun i => hb.slotAllows i.succ.succ) ha.slotAllows
        let sc := s.support pb pa (fun i => hb.used_nonzero (i := i.succ.succ)) (fun i => ha.used_nonzero)
        have ea : denoteSeq M ha = M.toSeqData.compose (weaken M.toSeqData wr) (denoteSeq M hac) :=
          denoteSeq_restrict_to M ha _ (fun _ => id) _ wr
        have fa : denoteSeq M ka = M.toSeqData.compose (weaken M.toSeqData vr) (denoteSeq M kac) :=
          denoteSeq_restrict_to M ka _ (fun _ => id) _ vr
        have eb : denoteSeq M hb = M.toSeqData.compose
            (M.toSeqData.right (M.toSeqData.right (weaken M.toSeqData wl) P) Q) (denoteSeq M hbc) := by
          rw [denoteSeq_restrict_to M hb _ cb
            (by simp only [QCtx.restrict_snoc_true]; exact congrArg (fun G => (G.snoc P).snoc Q) hbl)
            ((wl.keepNewest P).keepNewest Q), weaken_snoc M Q (wl.keepNewest P), weaken_snoc M P wl]
        have fb : denoteSeq M kb = M.toSeqData.compose
            (M.toSeqData.right (M.toSeqData.right (weaken M.toSeqData vl) P) Q) (denoteSeq M kbc) := by
          rw [denoteSeq_restrict_to M kb _ cb
            (by simp only [QCtx.restrict_snoc_true]; exact congrArg (fun G => (G.snoc P).snoc Q) kbl)
            ((vl.keepNewest P).keepNewest Q), weaken_snoc M Q (vl.keepNewest P), weaken_snoc M P vl]
        change M.toSeqData.compose (split M.toSeqData s)
          (M.toSeqData.compose (M.toSeqData.left _ (denoteSeq M ha))
            (M.toSeqData.compose (M.toSeqData.associatorInv _ _ _) (denoteSeq M hb))) =
          M.toSeqData.compose (split M.toSeqData t)
            (M.toSeqData.compose (M.toSeqData.left _ (denoteSeq M ka))
              (M.toSeqData.compose (M.toSeqData.associatorInv _ _ _) (denoteSeq M kb)))
        rw [ea, eb, fa, fb,
          ← M.toSeqData.compose_assoc (M.toSeqData.associatorInv _ _ _)
            (M.toSeqData.right (M.toSeqData.right (weaken M.toSeqData wl) _) _),
          ← M.toSeqData.associatorInv_natural_left (weaken M.toSeqData wl),
          ← M.toSeqData.compose_assoc (M.toSeqData.associatorInv _ _ _)
            (M.toSeqData.right (M.toSeqData.right (weaken M.toSeqData vl) _) _),
          ← M.toSeqData.associatorInv_natural_left (weaken M.toSeqData vl)]
        simp only [M.toSeqData.compose_assoc]
        rw [← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right (weaken M.toSeqData wl) _),
          ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl),
          ← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right (weaken M.toSeqData vl) _),
          ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ vl)]
        simp only [← M.toSeqData.compose_assoc]
        rw [← weaken_split M w s sc wl wr, ← weaken_split M w t sc vl vr,
          iha hac kac, ihb hbc kbc]
  | inl => cases h with | inl f => cases f
  | inr => cases h with | inr f => cases f
  | case => cases h with | case f => cases f
  | abort => cases h with | abort f => cases f
  | iter => cases h with | iter f => cases f

end Silmaril.Isotope.Refinement.Models.Denotation
