module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.BetaContexts
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqCoherence

/-! # Binder annotations in categorical beta reduction -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

/-- Changing a retained binder's annotation changes no packed wire. -/
theorem denoteSeq_binder_used {n : Nat} {Γ : QCtx (Ty α) n} {e η : ε}
    {b : Term Φ (n + 1)} {A B : Ty α} {q : Quantity}
    (hb : HasType .seq (Γ.snoc A (.used q)) e b B)
    (hd : HasType .seq (Γ.snoc A) η b B) : denoteSeq M hd = denoteSeq M hb :=
  Sequential.denote_binder_used M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) hb hd

/-- If a body accepts both zero and ordinary usage, the ordinary value is discardable. -/
theorem zero_binder_affine {F : Fragment} {n : Nat} {Γ : QCtx (Ty α) n} {e η : ε}
    {b : Term Φ (n + 1)} {A B : Ty α}
    (hb : HasType F (Γ.snoc A .zero) e b B)
    (hd : HasType F (Γ.snoc A) η b B) : Quantity.affine ≤ quantity A :=
  Sequential.zero_binder_affine hb hd

/-- The ordinary interpretation of a zero-use binder first discards that wire. -/
theorem denoteSeq_binder_zero {n : Nat} {Γ : QCtx (Ty α) n} {e η : ε}
    {b : Term Φ (n + 1)} {A B : Ty α}
    (hb : HasType .seq (Γ.snoc A .zero) e b B)
    (hd : HasType .seq (Γ.snoc A) η b B) (hA : Quantity.affine ≤ quantity A) :
    denoteSeq M hd = M.compose
      (M.compose (M.left (packed Γ) (M.discard A hA)) (M.rightUnitor (packed Γ)))
      (denoteSeq M (Γ := Γ.snoc A .zero) hb) :=
  Sequential.denote_binder_zero M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) hb hd hA

end Silmaril.Isotope.Refinement.Models.Denotation
