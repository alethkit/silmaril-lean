module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterCoherence

/-! # Proved witness coherence for the three categorical model classes

These instances discharge the shared soundness prerequisites using native
typing comparison. They impose no additional laws on the model classes.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.seqWitnessCoherent (M : SeqModel.{u,v,w,r} (Ty α) Φ ε) :
    WitnessCoherent M (ControlData.seq M) := denoteSeq_coherent M

theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent (M : CaseModel.{u,v,w,r} (Ty α) Φ ε) :
    WitnessCoherent M.toSeqModel (ControlData.case M) := denoteCase_coherent M

theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent (M : IterModel.{u,v,w,r} (Ty α) Φ ε) :
    WitnessCoherent M.toSeqModel (ControlData.iter M) := denoteIter_coherent M

/-- Every derivation of a weakened case term has the structural meaning. -/
theorem denoteCase_rename_of_typing (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    {n m : Nat} {Δ : QCtx (Ty α) n} {Γ : QCtx (Ty α) m} {e e' : ε}
    {t : Term Φ n} {A : Ty α} (h : HasType .case Δ e t A)
    (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ)
    (k : HasType .case Γ e' (Tm.rename ρ t) A) :
    denoteCase M k = M.compose (weaken M.toSeqData w) (denoteCase M h) :=
  denote_rename_of_typing M.toSeqModel (ControlData.case M) (ControlEnvironment.case M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M) h ρ w k

/-- Coherence also covers the chosen native renaming derivation. -/
theorem denoteCase_rename (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    {n m : Nat} {Δ : QCtx (Ty α) n} {Γ : QCtx (Ty α) m} {e : ε}
    {t : Term Φ n} {A : Ty α} (h : HasType .case Δ e t A)
    (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ) :
    denoteCase M (h.rename ρ w) = M.compose (weaken M.toSeqData w) (denoteCase M h) :=
  denoteCase_rename_of_typing M h ρ w (h.rename ρ w)

/-- Every derivation of a weakened iteration term has the structural meaning. -/
theorem denoteIter_rename_of_typing (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {n m : Nat} {Δ : QCtx (Ty α) n} {Γ : QCtx (Ty α) m} {e e' : ε}
    {t : Term Φ n} {A : Ty α} (h : HasType .iter Δ e t A)
    (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ)
    (k : HasType .iter Γ e' (Tm.rename ρ t) A) :
    denoteIter M k = M.compose (weaken M.toSeqData w) (denoteIter M h) :=
  denote_rename_of_typing M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) h ρ w k

theorem denoteIter_rename (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {n m : Nat} {Δ : QCtx (Ty α) n} {Γ : QCtx (Ty α) m} {e : ε}
    {t : Term Φ n} {A : Ty α} (h : HasType .iter Δ e t A)
    (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ) :
    denoteIter M (h.rename ρ w) = M.compose (weaken M.toSeqData w) (denoteIter M h) :=
  denoteIter_rename_of_typing M h ρ w (h.rename ρ w)

end Silmaril.Isotope.Refinement.Models.Denotation
