module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Elimination
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.PairSoundness

/-! # Sound directed elimination in the written sequential calculus -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

/-- Discarding an ordinary unit binder is the right unitor. -/
theorem denoteSeq_lift_unit {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε}
    {b : Term Φ n} {B : Ty α} (hb : HasType .seq Γ e b B)
    (hk : HasType .seq (Γ.snoc Silmaril.unit) e' b.lift B) :
    denoteSeq M hk = M.compose (M.rightUnitor (packed Γ)) (denoteSeq M hb) :=
  Sequential.denote_lift_unit M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) hb hk

set_option backward.isDefEq.respectTransparency false in
/-- The effect-dependent elimination rule is valid even when retained
ambient variables have linear types. -/
theorem denoteSeq_eliminate (p : Polarity) {n : Nat} {Γ Γl : QCtx (Ty α) n}
    {e η eL eR : ε} {a b : Term Φ n} {B : Ty α}
    (s : Γ.Split Γl Γ) (ha : HasType .seq Γl e a Silmaril.unit)
    (hd : Usage.zero ≤ Usage.used (EffectSystem.quantity p e))
    (hb : HasType .seq Γ η b B)
    (hl : HasType .seq Γ eL (.let₁ a b.lift) B)
    (hr : HasType .seq Γ eR (.let₁ .unit b.lift) B) :
    p.orient M.le (denoteSeq M hl) (denoteSeq M hr) :=
  Sequential.denote_eliminate M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) (ControlEffects.seq M) p s ha hd hb hl hr

end Silmaril.Isotope.Refinement.Models.Denotation
