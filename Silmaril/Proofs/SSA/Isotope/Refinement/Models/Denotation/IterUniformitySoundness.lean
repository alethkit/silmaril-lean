module

public import Silmaril.Raw.SSA.Isotope.Refinement.Laws
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.UniformityEvaluation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.UniformitySimulation

/-! # Soundness of the written directed uniformity rule -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} (Ty α) Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Directed uniformity preserves a possibly linear comparison context. The
original left loop body is effect bounded; the right loop and exit remain unrestricted. -/
theorem denoteIter_uniformity_square (p : Polarity) {n : Nat}
    {Γ Γl Γr Γc : QCtx (Ty α) n} {a : Term Φ n}
    {s b b' c : Term Φ (n + 1)} {A B C S : Ty α} {e η : ε}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γc)
    (hu : Γl.linearity = ⊤) (he : EffectSystem.iterable e)
    (ha : HasType .iter Γr e a A) (hs : HasType .iter (Γc.snoc A) η s S)
    (hb : HasType .iter (Γl.snoc S) e b (coprod C S))
    (hb' : HasType .iter (Γl.snoc A) (⊤ : ε) b' (coprod B A))
    (hc : HasType .iter (Γc.snoc B) (⊤ : ε) c C)
    (hm : EffectSystem.moves p η e)
    (hpl : HasType .iter (Γc.snoc A) (⊤ : ε) (.let₁ s b.underBinder) (coprod C S))
    (hpr : HasType .iter (Γc.snoc A) (⊤ : ε)
      (.case b' (.inl c.underBinder) (.inr s.underBinder)) (coprod C S))
    (hl : HasType .iter Γ (⊤ : ε) (.let₁ a (.iter s b.underBinder)) C)
    (hr : HasType .iter Γ (⊤ : ε) (.let₁ (.iter a b') c) C)
    (hp : p.orient M.le (denoteIter M hpl) (denoteIter M hpr)) :
    p.orient M.le (denoteIter M hl) (denoteIter M hr) := by
  have hdl : Γl.Discardable := QCtx.discardable_iff_linearity.mpr (hu ▸ le_top)
  let cD : Quantity.relevant ≤ quantity (packed Γl) := inner.relevant_retained.trans (packed_quantity Γl)
  let dD : Quantity.affine ≤ quantity (packed Γl) := discardable_quantity hdl
  let j := splitRightCoaction M.toSeqModel inner hdl
  let state : M.Hom (product (packed Γc) A) (product (packed Γl) S) :=
    M.compose (M.toSeqData.contextAction (split M.toSeqData inner) A)
      (M.left (packed Γl) (denoteIter M hs))
  let body : M.Hom (product (packed Γl) S) (coprod C (product (packed Γl) S)) :=
    (ControlData.iter M).contextStep trivial (packed Γl) cD dD (denoteIter M hb)
  let step : M.Hom (product (packed Γc) A) (coprod (product (packed Γc) B) (product (packed Γc) A)) :=
    M.compose (M.toSeqData.contextAction (split M.toSeqData inner.symm) A)
      (M.compose (M.left (packed Γc) (denoteIter M hb')) (M.distribute (packed Γc) B A))
  have hp' : p.orient M.le (M.compose state (denoteIter M hb))
      (M.compose step (M.desc (M.compose (denoteIter M hc) (M.inl C S))
        (M.compose (denoteIter M hs) (M.inr C S)))) := by
    rw [denoteIter_uniformity_premise_left M inner hs hb hpl,
      denoteIter_uniformity_premise_right M inner hs hb' hc hpr] at hp
    simpa only [state, step, SeqData.contextAction, M.compose_assoc] using hp
  have hsq := M.contextAction_uniformity_square p
    (split M.toSeqData inner) (split M.toSeqData inner.symm) (split_pure _ _) (split_pure _ _)
    cD dD (split_left_coassoc M.toSeqModel inner) (split_mixed_coassoc M.toSeqModel inner)
    (split_left_counit M.toSeqModel inner hdl)
    (denoteIter M hs) (denoteIter M hb) (denoteIter M hb') (denoteIter M hc) hp'
  have hstate : M.hasEffect η state :=
    M.compose_effect (M.effect_mono bot_le (M.toSeqData.contextAction_pure _ (split_pure _ _) A))
      (M.left_effect _ (denoteIter_effect M hs))
  have hbody : M.hasEffect e body := by
    apply M.compose_effect (M.effect_mono bot_le (M.right_effect _ (M.copy_pure _ cD)))
    apply M.compose_effect (M.effect_mono bot_le (M.associator_pure _ _ _))
    apply M.compose_effect (M.left_effect _ (denoteIter_effect M hb))
    apply M.compose_effect (M.effect_mono bot_le (M.toCaseData.distribute_pure _ _ _))
    apply M.toCaseData.desc_effect
    · apply M.compose_effect (M.effect_mono bot_le (M.right_effect _ (M.discard_pure _ dD)))
      exact M.compose_effect (M.effect_mono bot_le (M.leftUnitor_pure _))
        (M.effect_mono bot_le (M.toCaseData.inl_pure _ _))
    · exact M.effect_mono bot_le (M.toCaseData.inr_pure _ _)
  have hloop := M.mixed_uniformity p state (denoteIter M hc) body step he hm hstate hbody hsq
  have hright : M.iterate step = M.compose (M.toSeqData.contextAction (split M.toSeqData inner.symm) A)
      (M.left (packed Γc) ((ControlData.iter M).iterateWithContext trivial (packed Γl) cD dD (denoteIter M hb'))) :=
    (M.coaction_iterate j (denoteIter M hb')).symm
  rw [hright] at hloop
  have hresult := M.toSeqData.orient_compose_left p hloop
    (M.compose (split M.toSeqData outer) (M.left (packed Γc) (denoteIter M ha)))
  rw [denoteIter_uniformity_conclusion_left M outer inner hu ha hs hb cD dD hl,
    denoteIter_uniformity_conclusion_right M outer inner hu ha hb' hc cD dD hr]
  simpa only [state, body, ControlData.iterateWithContext, ControlData.iter, ControlData.ofCase,
    SeqData.contextAction, M.compose_assoc] using hresult

/-- Every instance of the written directed uniformity rule is categorically sound. -/
theorem denoteIter_uniformity {n m : Nat} {Γ : QCtx (Ty α) n} {Δ : QCtx (Ty α) m}
    {a b : Term Φ n} {c d : Term Φ m} {A B : Ty α} (p : Polarity)
    (rule : UniformityRule (ε := ε) .iter p Γ a b A Δ c d B)
    (ha : HasType .iter Γ (⊤ : ε) a A) (hb : HasType .iter Γ (⊤ : ε) b A)
    (hc : HasType .iter Δ (⊤ : ε) c B) (hd : HasType .iter Δ (⊤ : ε) d B)
    (hs : p.orient M.le (denoteIter M ha) (denoteIter M hb)) :
    p.orient M.le (denoteIter M hc) (denoteIter M hd) := by
  cases rule with
  | square _ outer inner hu he ha' hs' hb' hbb' hc' hm =>
    exact denoteIter_uniformity_square M p outer inner hu he ha' hs' hb' hbb' hc' hm ha hb hc hd hs

end Silmaril.Isotope.Refinement.Models.Denotation
