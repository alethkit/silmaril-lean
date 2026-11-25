module

public import Silmaril.SSA.Isotope.Refinement.Models.Defs
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqCaseRefinementSoundness
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterRefinementSoundness

/-! # Categorical soundness of the written quantitative let calculi

Each strict categorical model validates the written refinement closure of its
primitive rewrites. Typing witness coherence covers different effect bounds.
Soundness ranges over all quantitative contexts.
-/

public section

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r

variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)]
variable {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Sequential denotation is independent of the typing witness and effect bound. -/
theorem seqWitnessCoherent (M : SeqModel.{u,v,w,r} (Ty α) Φ ε) :
    WitnessCoherent M (ControlData.seq M) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.seqWitnessCoherent M

/-- Branching denotation is independent of the typing witness and effect bound. -/
theorem caseWitnessCoherent (M : CaseModel.{u,v,w,r} (Ty α) Φ ε) :
    WitnessCoherent M.toSeqModel (ControlData.case M) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M

/-- Iterative denotation is independent of the typing witness and effect bound. -/
theorem iterWitnessCoherent (M : IterModel.{u,v,w,r} (Ty α) Φ ε) :
    WitnessCoherent M.toSeqModel (ControlData.iter M) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M

/-- A sequential model validates the full written refinement closure of its primitive rewrites. -/
theorem seq_validates_refines (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)
    {R : Relation (Ty α) Φ} (hR : Validates M.toSeqData (ControlData.seq M) R) :
    Validates M.toSeqData (ControlData.seq M) (Refines (ε := ε) .seq R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.seq_validates_refines M hR

/-- A distributive model validates the full written refinement closure, including quantitative beta. -/
theorem case_validates_refines (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    {R : Relation (Ty α) Φ} (hR : Validates M.toSeqData (ControlData.case M) R) :
    Validates M.toSeqData (ControlData.case M) (Refines (ε := ε) .case R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.case_validates_refines M hR

/-- An iterative model validates the written closure, including effectful directed uniformity. -/
theorem iter_validates_refines (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {R : Relation (Ty α) Φ} (hR : Validates M.toSeqData (ControlData.iter M) R) :
    Validates M.toSeqData (ControlData.iter M) (Refines (ε := ε) .iter R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.iter_validates_refines M hR

end Silmaril.Isotope.Refinement.Models.Denotation
