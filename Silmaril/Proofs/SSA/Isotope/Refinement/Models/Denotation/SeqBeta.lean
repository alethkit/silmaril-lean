module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqSubstitution
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqBetaContexts
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Beta

/-! # Actual directed beta soundness for sequential syntax -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Quantitative beta constructs a native substituted endpoint and compares its
interpretation with execution of the initializer followed by the body. -/
theorem denoteSeq_beta_exists (p : Polarity) {n : Nat} {Γ Γl Γr : QCtx (Ty α) n}
    {e η : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : Ty α} {q : Usage}
    (s : Γ.Split Γl Γr) (ha : HasType .seq Γl e a A)
    (hb : HasType .seq (Γr.snoc A q) η b B)
    (hd : HasType .seq (Γr.snoc A) η b B)
    (hm : EffectSystem.moves p e η)
    (hq : q ≤ Usage.used (Γl.linearity ⊓ EffectSystem.quantity p e)) :
    ∃ k : HasType .seq Γ (e ⊔ η) (Tm.instantiate b a) B,
      p.orient M.le
        (M.compose (split M.toSeqData s.symm)
          (M.compose (M.left (packed Γr) (denoteSeq M ha)) (denoteSeq M hd)))
        (denoteSeq M k) :=
  Sequential.denote_beta_exists M (ControlData.seq M) (ControlEffects.seq M)
    (ControlEnvironment.seq M) (denoteSeq_coherent M) p (denoteSeq_bsubst_exists M p)
    s ha hb hd hm hq

/-- The written beta rule is sound for arbitrary typing witnesses of its endpoints. -/
theorem denoteSeq_beta (p : Polarity) {n : Nat} {Γ Γl Γr : QCtx (Ty α) n}
    {e η eL eR : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : Ty α} {q : Usage}
    (s : Γ.Split Γl Γr) (ha : HasType .seq Γl e a A)
    (hb : HasType .seq (Γr.snoc A q) η b B)
    (hd : HasType .seq (Γr.snoc A) η b B)
    (hm : EffectSystem.moves p e η)
    (hq : q ≤ Usage.used (Γl.linearity ⊓ EffectSystem.quantity p e))
    (hl : HasType .seq Γ eL (.let₁ a b) B)
    (hr : HasType .seq Γ eR (Tm.instantiate b a) B) :
    p.orient M.le (denoteSeq M hl) (denoteSeq M hr) :=
  Sequential.denote_beta M (ControlData.seq M) (ControlEffects.seq M)
    (ControlEnvironment.seq M) (denoteSeq_coherent M) p (denoteSeq_bsubst_exists M p)
    s ha hb hd hm hq hl hr

end Silmaril.Isotope.Refinement.Models.Denotation
