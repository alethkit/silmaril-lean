module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Renaming
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqCoherence

/-! # Sequential renaming soundness for every typing witness -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

/-- Any sequential derivation of weakened syntax has the structural interpretation. -/
theorem denoteSeq_rename_of_typing {n m : Nat} {Δ : QCtx (Ty α) n} {Γ : QCtx (Ty α) m}
    {e e' : ε} {t : Term Φ n} {A : Ty α} (h : HasType .seq Δ e t A)
    (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ)
    (k : HasType .seq Γ e' (Tm.rename ρ t) A) :
    denoteSeq M k = M.toSeqData.compose (weaken M.toSeqData w) (denoteSeq M h) := by
  obtain ⟨k', hk'⟩ := denote_rename_exists M (ControlData.seq M) (ControlEnvironment.seq M) h ρ w
  exact (denoteSeq_coherent M k k').trans hk'

/-- Typing coherence justifies interpretation of the existing chosen weakening witness. -/
theorem denoteSeq_rename {n m : Nat} {Δ : QCtx (Ty α) n} {Γ : QCtx (Ty α) m}
    {e : ε} {t : Term Φ n} {A : Ty α} (h : HasType .seq Δ e t A)
    (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ) :
    denoteSeq M (h.rename ρ w) = M.toSeqData.compose (weaken M.toSeqData w) (denoteSeq M h) :=
  denoteSeq_rename_of_typing M h ρ w (h.rename ρ w)

end Silmaril.Isotope.Refinement.Models.Denotation
