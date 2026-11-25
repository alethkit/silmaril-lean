module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonConstructors
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonSupport

/-! # Canonical support splits for binder comparison -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K)
include N

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq α] in
/-- A let derivation factors through independently restricted value and body supports. -/
theorem denote_let₁_support {n : Nat} {Γ Γl Γr : QCtx (Ty α) n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B : Ty α}
    (s : QCtx.Split Γ Γl Γr) (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b B) :
    denote M.toSeqData K (.let₁ s ha hb) =
      M.compose (weaken M.toSeqData (s.supportWeakening (fun i => Term.uses b i.succ) (Term.uses a)
        (fun i => hb.slotAllows i.succ) ha.slotAllows))
        (denote M.toSeqData K (.let₁ (s.restrictOutputs (fun i => Term.uses b i.succ) (Term.uses a)
          (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero)) ha.support hb.outerSupport₁)) := by
  let w := s.supportWeakening (fun i => Term.uses b i.succ) (Term.uses a)
    (fun i => hb.slotAllows i.succ) ha.slotAllows
  let sc := s.restrictOutputs (fun i => Term.uses b i.succ) (Term.uses a)
    (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero)
  change M.compose (split M.toSeqData s) (M.compose (M.left _ (denote M.toSeqData K ha)) (denote M.toSeqData K hb)) =
    M.compose (weaken M.toSeqData w) (M.compose (split M.toSeqData sc)
      (M.compose (M.left _ (denote M.toSeqData K ha.support)) (denote M.toSeqData K hb.outerSupport₁)))
  rw [denote_restrict M.toSeqModel K N ha _ (fun _ => id), denote_outerSupport₁ M.toSeqModel K N hb,
    ← M.compose_assoc (M.left _ _), ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ hb.outerWeakening₁)]
  simp only [← M.compose_assoc]
  exact congrArg (fun f => M.compose (M.compose f (M.left _ (denote M.toSeqData K ha.support)))
    (denote M.toSeqData K hb.outerSupport₁))
    (weaken_split M.toSeqModel w s sc hb.outerWeakening₁ ha.supportWeakening).symm

set_option backward.isDefEq.respectTransparency false in
/-- Let comparison does not depend on the original resource allocation witnesses. -/
theorem TypingComparison.let₁_support {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B C D : Ty α}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr) (hc : QCtx.Aligned Γ Δ)
    (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b B)
    (ka : HasType F Δr e' a C) (kb : HasType F (Δl.snoc C) e' b D)
    (ca : TypingComparison M K ha.support ka.support (ha.support_aligned ka))
    (cb : TypingComparison M K hb.outerSupport₁ kb.outerSupport₁ ((hb.outerSupport₁_aligned kb).snoc A C)) :
    TypingComparison M K (.let₁ s ha hb) (.let₁ t ka kb) hc := by
  let pb := fun i : Fin n => Term.uses b i.succ
  let pa := Term.uses a
  let p := fun i => pb i || pa i
  let sc := s.restrictOutputs pb pa (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero)
  let tc := t.restrictOutputs pb pa (fun i => kb.used_nonzero (i := i.succ)) (fun _ => ka.used_nonzero)
  let w := s.supportWeakening pb pa (fun i => hb.slotAllows i.succ) ha.slotAllows
  let v := t.supportWeakening pb pa (fun i => kb.slotAllows i.succ) ka.slotAllows
  exact TypingComparison.of_factors M K N (.let₁ s ha hb) (.let₁ t ka kb)
    (.let₁ sc ha.support hb.outerSupport₁) (.let₁ tc ka.support kb.outerSupport₁)
    w v (QCtx.weakening_merge_of_restrict w v) hc (hc.restrict p)
    (denote_let₁_support M K N s ha hb) (denote_let₁_support M K N t ka kb)
    (TypingComparison.let₁ M K sc tc (hc.restrict p) (hb.outerSupport₁_aligned kb) (ha.support_aligned ka)
      ((hb.outerSupport₁_aligned kb).snoc A C) ha.support hb.outerSupport₁ ka.support kb.outerSupport₁ ca cb)

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq α] in
/-- Product-let interpretation factors through value support and outer body support. -/
theorem denote_let₂_support {n : Nat} {Γ Γl Γr : QCtx (Ty α) n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n+2)} {A B C : Ty α}
    (s : QCtx.Split Γ Γl Γr) (ha : HasType F Γr e a (product A B))
    (hb : HasType F ((Γl.snoc A).snoc B) e b C) :
    denote M.toSeqData K (.let₂ s ha hb) =
      M.compose (weaken M.toSeqData (s.supportWeakening (fun i => Term.uses b i.succ.succ) (Term.uses a)
        (fun i => hb.slotAllows i.succ.succ) ha.slotAllows))
        (denote M.toSeqData K (.let₂ (s.restrictOutputs (fun i => Term.uses b i.succ.succ) (Term.uses a)
          (fun i => hb.used_nonzero (i := i.succ.succ)) (fun _ => ha.used_nonzero)) ha.support hb.outerSupport₂)) := by
  let w := s.supportWeakening (fun i => Term.uses b i.succ.succ) (Term.uses a)
    (fun i => hb.slotAllows i.succ.succ) ha.slotAllows
  let sc := s.restrictOutputs (fun i => Term.uses b i.succ.succ) (Term.uses a)
    (fun i => hb.used_nonzero (i := i.succ.succ)) (fun _ => ha.used_nonzero)
  change M.compose (split M.toSeqData s) (M.compose (M.left _ (denote M.toSeqData K ha))
      (M.compose (M.associatorInv _ A B) (denote M.toSeqData K hb))) =
    M.compose (weaken M.toSeqData w) (M.compose (split M.toSeqData sc)
      (M.compose (M.left _ (denote M.toSeqData K ha.support))
        (M.compose (M.associatorInv _ A B) (denote M.toSeqData K hb.outerSupport₂))))
  rw [denote_restrict M.toSeqModel K N ha _ (fun _ => id), denote_outerSupport₂ M.toSeqModel K N hb,
    ← M.compose_assoc (M.associatorInv _ A B), ← M.toSeqData.associatorInv_natural_left]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.left _ _), ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ hb.outerWeakening₂)]
  simp only [← M.compose_assoc]
  exact congrArg (fun f => M.compose (M.compose (M.compose f (M.left _ (denote M.toSeqData K ha.support)))
    (M.associatorInv _ A B)) (denote M.toSeqData K hb.outerSupport₂))
    (weaken_split M.toSeqModel w s sc hb.outerWeakening₂ ha.supportWeakening).symm

set_option backward.isDefEq.respectTransparency false in
/-- Product-let comparison uses the common raw supports of both hidden binders. -/
theorem TypingComparison.let₂_support {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {b : Term Φ (n+2)} {A B C D E G : Ty α}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr) (hc : QCtx.Aligned Γ Δ)
    (ha : HasType F Γr e a (product A B)) (hb : HasType F ((Γl.snoc A).snoc B) e b E)
    (ka : HasType F Δr e' a (product C D)) (kb : HasType F ((Δl.snoc C).snoc D) e' b G)
    (ca : TypingComparison M K ha.support ka.support (ha.support_aligned ka))
    (cb : TypingComparison M K hb.outerSupport₂ kb.outerSupport₂ (((hb.outerSupport₂_aligned kb).snoc A C).snoc B D)) :
    TypingComparison M K (.let₂ s ha hb) (.let₂ t ka kb) hc := by
  let pb := fun i : Fin n => Term.uses b i.succ.succ
  let pa := Term.uses a
  let p := fun i => pb i || pa i
  let sc := s.restrictOutputs pb pa (fun i => hb.used_nonzero (i := i.succ.succ)) (fun _ => ha.used_nonzero)
  let tc := t.restrictOutputs pb pa (fun i => kb.used_nonzero (i := i.succ.succ)) (fun _ => ka.used_nonzero)
  let w := s.supportWeakening pb pa (fun i => hb.slotAllows i.succ.succ) ha.slotAllows
  let v := t.supportWeakening pb pa (fun i => kb.slotAllows i.succ.succ) ka.slotAllows
  exact TypingComparison.of_factors M K N (.let₂ s ha hb) (.let₂ t ka kb)
    (.let₂ sc ha.support hb.outerSupport₂) (.let₂ tc ka.support kb.outerSupport₂)
    w v (QCtx.weakening_merge_of_restrict w v) hc (hc.restrict p)
    (denote_let₂_support M K N s ha hb) (denote_let₂_support M K N t ka kb)
    (TypingComparison.let₂ M K sc tc (hc.restrict p) (hb.outerSupport₂_aligned kb) (ha.support_aligned ka)
      (((hb.outerSupport₂_aligned kb).snoc A C).snoc B D) ha.support hb.outerSupport₂ ka.support kb.outerSupport₂ ca cb)

end Silmaril.Isotope.Refinement.Models.Denotation
