module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonSupport

/-! # Canonical support splits for iteration comparison -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K)
include N

omit [DecidableEq α] in
set_option backward.isDefEq.respectTransparency false in
/-- Loop interpretation factors through the actual supports of its initial
state and retained body environment. Unrestrictedness survives restriction. -/
theorem denote_iter_support {n : Nat} {Γ Γl Γr : QCtx (Ty α) n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B : Ty α}
    (cap : F.HasIter) (s : QCtx.Split Γ Γl Γr)
    (hu : Γl.linearity = ⊤) (hi : EffectSystem.iterable e)
    (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (.coprod B A)) :
    denote M.toSeqData K (.iter cap s hu hi ha hb) =
      M.compose (weaken M.toSeqData (s.supportWeakening (fun i => Term.uses b i.succ) (Term.uses a)
        (fun i => hb.slotAllows i.succ) ha.slotAllows))
        (denote M.toSeqData K (.iter cap
          (s.restrictOutputs (fun i => Term.uses b i.succ) (Term.uses a)
            (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero))
          (QCtx.restrict_unrestricted hu _) hi ha.support hb.outerSupport₁)) := by
  let pb := fun (i : Fin n) => Term.uses b i.succ
  let w := s.supportWeakening pb (Term.uses a) (fun i => hb.slotAllows i.succ) ha.slotAllows
  let sc := s.restrictOutputs pb (Term.uses a)
    (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero)
  have qD : (⊤ : Quantity) ≤ quantity (packed Γl) := hu ▸ packed_quantity Γl
  have qE : (⊤ : Quantity) ≤ quantity (packed (Γl.restrict pb)) :=
    (QCtx.restrict_unrestricted hu pb) ▸ packed_quantity (Γl.restrict pb)
  let cD : Quantity.relevant ≤ quantity (packed Γl) := le_top.trans qD
  let dD : Quantity.affine ≤ quantity (packed Γl) := le_top.trans qD
  let cE : Quantity.relevant ≤ quantity (packed (Γl.restrict pb)) := le_top.trans qE
  let dE : Quantity.affine ≤ quantity (packed (Γl.restrict pb)) := le_top.trans qE
  let loop := K.iterateWithContext cap (packed (Γl.restrict pb)) cE dE (denote M.toSeqData K hb.outerSupport₁)
  have hloop : K.iterateWithContext cap (packed Γl) cD dD (denote M.toSeqData K hb) =
      M.compose (M.right (weaken M.toSeqData hb.outerWeakening₁) A) loop := by
    rw [denote_outerSupport₁ M.toSeqModel K N hb]
    exact (N.iter_natural cap _ (weaken_pure _ hb.outerWeakening₁) cD dD cE dE _).symm
  change M.compose (split M.toSeqData s)
      (M.compose (M.left _ (denote M.toSeqData K ha))
        (K.iterateWithContext cap (packed Γl) cD dD (denote M.toSeqData K hb))) =
    M.compose (weaken M.toSeqData w) (M.compose (split M.toSeqData sc)
      (M.compose (M.left _ (denote M.toSeqData K ha.support)) loop))
  rw [denote_restrict M.toSeqModel K N ha _ (fun _ => id), hloop,
    ← M.compose_assoc (M.left _ _), ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ hb.outerWeakening₁)]
  simp only [← M.compose_assoc]
  exact congrArg (fun f => M.compose (M.compose f (M.left _ (denote M.toSeqData K ha.support))) loop)
    (weaken_split M.toSeqModel w s sc hb.outerWeakening₁ ha.supportWeakening).symm

set_option backward.isDefEq.respectTransparency false in
/-- A common typing for support-normalized loops lifts to arbitrary original
resource allocations. The caller supplies the proved aligned iteration rule. -/
theorem TypingComparison.iter_support {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B C D : Ty α}
    (cap : F.HasIter) (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (ug : Γl.linearity = ⊤) (ud : Δl.linearity = ⊤)
    (ie : EffectSystem.iterable e) (ie' : EffectSystem.iterable e')
    (hc : QCtx.Aligned Γ Δ)
    (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (.coprod B A))
    (ka : HasType F Δr e' a C) (kb : HasType F (Δl.snoc C) e' b (.coprod D C))
    (cn : TypingComparison M K
      (.iter cap (s.restrictOutputs (fun i => Term.uses b i.succ) (Term.uses a)
          (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero))
        (QCtx.restrict_unrestricted ug _) ie ha.support hb.outerSupport₁)
      (.iter cap (t.restrictOutputs (fun i => Term.uses b i.succ) (Term.uses a)
          (fun i => kb.used_nonzero (i := i.succ)) (fun _ => ka.used_nonzero))
        (QCtx.restrict_unrestricted ud _) ie' ka.support kb.outerSupport₁)
      (hc.restrict (fun i => Term.uses b i.succ || Term.uses a i))) :
    TypingComparison M K (.iter cap s ug ie ha hb) (.iter cap t ud ie' ka kb) hc := by
  let pb := fun (i : Fin n) => Term.uses b i.succ
  let pa := Term.uses a
  let p := fun i => pb i || pa i
  let sc := s.restrictOutputs pb pa (fun i => hb.used_nonzero (i := i.succ)) (fun _ => ha.used_nonzero)
  let tc := t.restrictOutputs pb pa (fun i => kb.used_nonzero (i := i.succ)) (fun _ => ka.used_nonzero)
  let w := s.supportWeakening pb pa (fun i => hb.slotAllows i.succ) ha.slotAllows
  let v := t.supportWeakening pb pa (fun i => kb.slotAllows i.succ) ka.slotAllows
  exact TypingComparison.of_factors M K N (.iter cap s ug ie ha hb) (.iter cap t ud ie' ka kb)
    (.iter cap sc (QCtx.restrict_unrestricted ug _) ie ha.support hb.outerSupport₁)
    (.iter cap tc (QCtx.restrict_unrestricted ud _) ie' ka.support kb.outerSupport₁)
    w v (QCtx.weakening_merge_of_restrict w v) hc (hc.restrict p)
    (denote_iter_support M K N cap s ug ie ha hb) (denote_iter_support M K N cap t ud ie' ka kb) cn

end Silmaril.Isotope.Refinement.Models.Denotation
