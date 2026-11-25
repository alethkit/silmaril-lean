module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Retention
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence

/-! # Directed elimination shared by every control fragment -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K) (H : WitnessCoherent M K)
variable (E : ControlEffects K)

namespace Sequential
include N H

/-- Discarding an ordinary unit binder is the right unitor. -/
theorem denote_lift_unit {n : Nat} {Γ : QCtx τ n} {e e' : ε}
    {b : Term Φ n} {B : τ} (hb : HasType F Γ e b B)
    (hk : HasType F (Γ.snoc Silmaril.unit) e' b.lift B) :
    denote M.toSeqData K hk = M.compose (M.rightUnitor (packed Γ)) (denote M.toSeqData K hb) := by
  have hz : Usage.zero ≤ Usage.effective (.used ⊤) (quantity (Silmaril.unit : τ)) := by
    rw [TypeQuantity.unit_quantity, Usage.effective_used]
    decide
  let w : QCtx.Weakening (Γ.snoc Silmaril.unit) Γ Fin.succ := .skip (.refl Γ) hz
  have hw : weaken M.toSeqData w = M.rightUnitor (packed Γ) := by
    have h := congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ) hz)
    change weaken M.toSeqData w =
      M.compose (M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) Silmaril.unit)
        (M.compose (M.left (packed Γ) (M.discard Silmaril.unit _)) (M.rightUnitor (packed Γ))) at h
    rw [weaken_refl, M.discard_unit, M.toSeqData.right_identity, M.toSeqData.left_identity,
      M.toSeqData.identity_compose, M.toSeqData.identity_compose] at h
    exact h
  exact (denote_rename_of_typing M K N H hb Fin.succ w hk).trans
    (congrArg (fun f => M.compose f (denote M.toSeqData K hb)) hw)

include E in
set_option backward.isDefEq.respectTransparency false in
/-- The effect-dependent elimination rule is valid even when retained
ambient variables have linear types. -/
theorem denote_eliminate (p : Polarity) {n : Nat} {Γ Γl : QCtx τ n}
    {e η eL eR : ε} {a b : Term Φ n} {B : τ}
    (s : Γ.Split Γl Γ) (ha : HasType F Γl e a Silmaril.unit)
    (hd : Usage.zero ≤ Usage.used (EffectSystem.quantity p e))
    (hb : HasType F Γ η b B)
    (hl : HasType F Γ eL (.let₁ a b.lift) B)
    (hr : HasType F Γ eR (.let₁ .unit b.lift) B) :
    p.orient M.le (denote M.toSeqData K hl) (denote M.toSeqData K hr) := by
  have hz : Usage.zero ≤ Usage.effective (.used ⊤) (quantity (Silmaril.unit : τ)) := by
    rw [TypeQuantity.unit_quantity, Usage.effective_used]
    decide
  let kb := hb.top.rename Fin.succ (QCtx.Weakening.skip (QCtx.Weakening.refl Γ) hz)
  have hk : denote M.toSeqData K kb = M.compose (M.rightUnitor (packed Γ)) (denote M.toSeqData K hb) :=
    denote_lift_unit M K N H hb kb
  have hleft : denote M.toSeqData K hl =
      M.compose (M.compose (split M.toSeqData s.symm)
        (M.compose (M.left (packed Γ) (denote M.toSeqData K ha)) (M.rightUnitor (packed Γ))))
        (denote M.toSeqData K hb) := by
    rw [H hl (.let₁ s.symm ha.top kb)]
    change M.compose (split M.toSeqData s.symm)
      (M.compose (M.left (packed Γ) (denote M.toSeqData K ha.top)) (denote M.toSeqData K kb)) = _
    rw [hk, H ha.top ha]
    simp only [M.toSeqData.compose_assoc]
  have hright : denote M.toSeqData K hr = denote M.toSeqData K hb := by
    let hu : HasType F Γ.zero (⊤ : ε) (.unit : Term Φ n) Silmaril.unit :=
      .unit (QCtx.zero_discardable Γ)
    rw [H hr (.let₁ (QCtx.Split.zero_right Γ) hu kb)]
    change M.compose (split M.toSeqData (QCtx.Split.zero_right Γ))
      (M.compose (M.left (packed Γ) (discard M.toSeqData (QCtx.zero_discardable Γ)))
        (denote M.toSeqData K kb)) = _
    rw [hk]
    have h := congrArg (fun f => M.compose f (denote M.toSeqData K hb))
      (zero_unit_bind M Γ (QCtx.zero_discardable Γ))
    simpa only [M.toSeqData.compose_assoc, M.toSeqData.identity_compose] using h
  rw [hleft, hright]
  have he : EffectSystem.canDelete p e := (Usage.zero_le_used _).mp hd
  have h := M.toSeqData.orient_compose_right p
    (retained_elimination M p s (denote M.toSeqData K ha) he (denote_effect K E ha)) (denote M.toSeqData K hb)
  simpa only [M.toSeqData.identity_compose] using h

end Sequential
end Silmaril.Isotope.Refinement.Models.Denotation
