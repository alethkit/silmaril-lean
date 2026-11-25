module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.RefinementSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqBeta
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseBeta
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqElimination
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseEquationSoundness

/-! # Categorical soundness of the written sequential and branching calculi -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Every written sequential directed axiom holds under its original resource
and effect conditions, for arbitrary endpoint typing witnesses. -/
theorem denoteSeq_directional (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)
    (p : Polarity) {n : Nat} {Γ : QCtx (Ty α) n} {a b : Term Φ n} {A : Ty α}
    {e η : ε} (h : DirectionalAxiom (ε := ε) .seq p Γ a b A)
    (ha : HasType .seq Γ e a A) (hb : HasType .seq Γ η b A) :
    p.orient M.le (denoteSeq M ha) (denoteSeq M hb) := by
  cases h with
  | eliminate s hd hq he => exact denoteSeq_eliminate M p s hd hq he ha hb
  | beta s hd he hf hm hq => exact denoteSeq_beta M p s hd he hf hm hq ha hb

/-- Every written branching directed axiom holds in a distributive model. -/
theorem denoteCase_directional (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    (p : Polarity) {n : Nat} {Γ : QCtx (Ty α) n} {a b : Term Φ n} {A : Ty α}
    {e η : ε} (h : DirectionalAxiom (ε := ε) .case p Γ a b A)
    (ha : HasType .case Γ e a A) (hb : HasType .case Γ η b A) :
    p.orient M.le (denoteCase M ha) (denoteCase M hb) := by
  cases h with
  | eliminate s hd hq he => exact denoteCase_eliminate M p s hd hq he ha hb
  | beta s hd he hf hm hq => exact denoteCase_beta M p s hd he hf hm hq ha hb

/-- Any sequential categorical model validating the primitive presentation
validates its full written refinement closure. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.seq_validates_refines (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)
    {R : Relation (Ty α) Φ} (hR : Validates M.toSeqData (ControlData.seq M) R) :
    Validates M.toSeqData (ControlData.seq M) (Refines (ε := ε) .seq R) := by
  refine validates_refines M (ControlData.seq M) (ControlMonotone.seq M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.seqWitnessCoherent M) (denoteSeq_equation M) (fun p h ha hb => denoteSeq_directional M p h ha hb) ?_ hR
  intro n m Γ Δ a b c d A B p h
  cases h with
  | square cap => exact False.elim cap

/-- Any distributive categorical model validating the primitive presentation
validates the full written refinement closure, including quantitative beta. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.case_validates_refines (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    {R : Relation (Ty α) Φ} (hR : Validates M.toSeqData (ControlData.case M) R) :
    Validates M.toSeqData (ControlData.case M) (Refines (ε := ε) .case R) := by
  refine validates_refines M.toSeqModel (ControlData.case M) (ControlMonotone.case M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M) (denoteCase_equation M) (fun p h ha hb => denoteCase_directional M p h ha hb) ?_ hR
  intro n m Γ Δ a b c d A B p h
  cases h with
  | square cap => exact False.elim cap

end Silmaril.Isotope.Refinement.Models.Denotation
