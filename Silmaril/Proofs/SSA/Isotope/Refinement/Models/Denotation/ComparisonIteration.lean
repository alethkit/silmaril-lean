module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.TypingComparison
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationSimulation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionTensor

/-! # Common typings for iteration with independent hidden state types -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
local notation "K" => ControlData.ofCase M.toCaseData F (fun _ => M.iterate)

set_option backward.isDefEq.respectTransparency false in
/-- Joint loop typing uses a common hidden state, with both original loops
related by the model's proved mixed simulation law. -/
theorem TypingComparison.iter {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {b : Term Φ (n + 1)} {A B C D : Ty α}
    (cap : F.HasIter) (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (ug : Γl.linearity = ⊤) (ud : Δl.linearity = ⊤)
    (ie : EffectSystem.iterable e) (ie' : EffectSystem.iterable e')
    (hc : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr)
    (hbctx : QCtx.Aligned (Γl.snoc A) (Δl.snoc C))
    (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (.coprod B A))
    (ka : HasType F Δr e' a C) (kb : HasType F (Δl.snoc C) e' b (.coprod D C))
    (ca : TypingComparison M.toCaseData K ha ka hr)
    (cb : TypingComparison M.toCaseData K hb kb hbctx) :
    TypingComparison M.toCaseData K (.iter cap s ug ie ha hb) (.iter cap t ud ie' ka kb) hc := by
  obtain ⟨la, hla, kla⟩ := ca
  obtain ⟨lb, hlb, klb⟩ := cb
  have he : QCtx.merge (Γl.snoc A) (Δl.snoc C) = (QCtx.merge Γl Δl).snoc (mergeType A C) := by simp
  let lb' := lb.castContext he
  have eb : denote M.toSeqData K lb' = denote M.toSeqData K lb :=
    eq_of_heq (denote_castContext_heq M.toSeqData K lb he)
  rw [← eb] at hlb klb
  have um := QCtx.merge_unrestricted ug ud
  have qg : (⊤ : Quantity) ≤ quantity (packed Γl) := ug ▸ packed_quantity Γl
  have qd : (⊤ : Quantity) ≤ quantity (packed Δl) := ud ▸ packed_quantity Δl
  have qm : (⊤ : Quantity) ≤ quantity (packed (QCtx.merge Γl Δl)) := um ▸ packed_quantity (QCtx.merge Γl Δl)
  let cg : Quantity.relevant ≤ quantity (packed Γl) := le_top.trans qg
  let dg : Quantity.affine ≤ quantity (packed Γl) := le_top.trans qg
  let cd : Quantity.relevant ≤ quantity (packed Δl) := le_top.trans qd
  let dd : Quantity.affine ≤ quantity (packed Δl) := le_top.trans qd
  let cm : Quantity.relevant ≤ quantity (packed (QCtx.merge Γl Δl)) := le_top.trans qm
  let dm : Quantity.affine ≤ quantity (packed (QCtx.merge Γl Δl)) := le_top.trans qm
  let loop := (ControlData.iter M).iterateWithContext trivial (packed (QCtx.merge Γl Δl)) cm dm
    (denote M.toSeqData K lb')
  have egl : M.compose ((K).iterateWithContext cap (packed Γl) cg dg (denote M.toSeqData K hb))
      (mergeLeft M.toCaseData B D) =
    M.compose (M.tensor (mergeContext M.toCaseData Γl Δl hl).1.1 (mergeLeft M.toCaseData A C)) loop := by
    apply Eq.symm
    apply M.iterateWithContext_simulation cg dg cm dm
      (mergeContext M.toCaseData Γl Δl hl).1.1 (mergeLeft M.toCaseData A C) (mergeLeft M.toCaseData B D)
      (mergeContext M.toCaseData Γl Δl hl).1.2 (mergeLeft_pure M.toCaseData A C)
    exact hlb.symm
  have egr : M.compose ((K).iterateWithContext cap (packed Δl) cd dd (denote M.toSeqData K kb))
      (mergeRight M.toCaseData B D) =
    M.compose (M.tensor (mergeContext M.toCaseData Γl Δl hl).2.1 (mergeRight M.toCaseData A C)) loop := by
    apply Eq.symm
    apply M.iterateWithContext_simulation cd dd cm dm
      (mergeContext M.toCaseData Γl Δl hl).2.1 (mergeRight M.toCaseData A C) (mergeRight M.toCaseData B D)
      (mergeContext M.toCaseData Γl Δl hl).2.2 (mergeRight_pure M.toCaseData A C)
    exact klb.symm
  refine ⟨.iter cap (s.merge t hl hr) um EffectSystem.iterable_top la lb', ?_, ?_⟩
  · change M.compose (M.compose (split M.toSeqData s)
      (M.compose (M.left _ (denote M.toSeqData K ha))
        ((K).iterateWithContext cap (packed Γl) cg dg (denote M.toSeqData K hb)))) (mergeLeft M.toCaseData B D) =
      M.compose (mergeContext M.toCaseData Γ Δ hc).1.1
        (M.compose (split M.toSeqData (s.merge t hl hr)) (M.compose (M.left _ (denote M.toSeqData K la)) loop))
    simp only [M.compose_assoc]
    rw [egl, ← M.compose_assoc (M.left _ (denote M.toSeqData K ha))]
    have hx : M.compose (M.left _ (denote M.toSeqData K ha))
        (M.tensor (mergeContext M.toCaseData Γl Δl hl).1.1 (mergeLeft M.toCaseData A C)) =
      M.tensor (mergeContext M.toCaseData Γl Δl hl).1.1
        (M.compose (denote M.toSeqData K ha) (mergeLeft M.toCaseData A C)) := by
      unfold SeqData.tensor
      rw [← M.compose_assoc, ← M.toSeqData.exchange_left_pure _ _ (mergeContext M.toCaseData Γl Δl hl).1.2,
        M.compose_assoc, ← M.left_compose]
    rw [hx, hla, ← M.toSeqData.tensor_left_after]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose f (M.left _ (denote M.toSeqData K la))) loop)
      (congrArg Subtype.val (mergeContext_split_fst M.toCaseData s t hc hl hr)).symm
  · change M.compose (M.compose (split M.toSeqData t)
      (M.compose (M.left _ (denote M.toSeqData K ka))
        ((K).iterateWithContext cap (packed Δl) cd dd (denote M.toSeqData K kb)))) (mergeRight M.toCaseData B D) =
      M.compose (mergeContext M.toCaseData Γ Δ hc).2.1
        (M.compose (split M.toSeqData (s.merge t hl hr)) (M.compose (M.left _ (denote M.toSeqData K la)) loop))
    simp only [M.compose_assoc]
    rw [egr, ← M.compose_assoc (M.left _ (denote M.toSeqData K ka))]
    have hx : M.compose (M.left _ (denote M.toSeqData K ka))
        (M.tensor (mergeContext M.toCaseData Γl Δl hl).2.1 (mergeRight M.toCaseData A C)) =
      M.tensor (mergeContext M.toCaseData Γl Δl hl).2.1
        (M.compose (denote M.toSeqData K ka) (mergeRight M.toCaseData A C)) := by
      unfold SeqData.tensor
      rw [← M.compose_assoc, ← M.toSeqData.exchange_left_pure _ _ (mergeContext M.toCaseData Γl Δl hl).2.2,
        M.compose_assoc, ← M.left_compose]
    rw [hx, kla, ← M.toSeqData.tensor_left_after]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose f (M.left _ (denote M.toSeqData K la))) loop)
      (congrArg Subtype.val (mergeContext_split_snd M.toCaseData s t hc hl hr)).symm

end Silmaril.Isotope.Refinement.Models.Denotation
