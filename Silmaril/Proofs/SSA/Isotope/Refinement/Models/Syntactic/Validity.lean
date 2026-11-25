module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ContextualValidity
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Reification
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseReification
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterReification
public import Silmaril.Raw.SSA.Isotope.Refinement.RewriteSystem

/-! # Syntactic models validate their native rewrite presentations

Validity includes arbitrary quantitative contexts and arbitrary endpoint
typing witnesses. The primitive presentation must be stable under native
weakening and pure substitution; the latter removes omitted context slots.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models.Syntactic
open Denotation
universe u v w
variable {α : Type u} [HasQuantity α]
variable {Φ : Type v} [HasTy Φ (Ty α)]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation (Ty α) Φ}

/-- The native sequential quotient validates its whole generated directed theory. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.seqModel_refines_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .seq R) :
    Validates (seqModel (ε := ε) (F := .seq) (R := R) hR).toSeqData
      (ControlData.seq (seqModel (F := .seq) (R := R) hR)) (Refines (ε := ε) .seq R) := by
  let M := seqModel (ε := ε) (F := .seq) (R := R) hR
  apply validates_of_singleton M (ControlData.seq M) (ControlEnvironment.seq M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.seqWitnessCoherent M) hR hS
  intro A B a b e η hr ha hb
  change le (denoteSeq M ha) (denoteSeq M hb)
  rw [denoteSeq_arrow hR ha, denoteSeq_arrow hR hb]
  exact compose_mono hR le_rfl hr

/-- The native case quotient validates its whole generated directed theory. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.caseModel_refines_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .case R) :
    Validates (caseModel (ε := ε) (F := .case) (R := R) hR trivial).toSeqData
      (ControlData.case (caseModel (F := .case) (R := R) hR trivial)) (Refines (ε := ε) .case R) := by
  let M := caseModel (ε := ε) (F := .case) (R := R) hR trivial
  apply validates_of_singleton M.toSeqModel (ControlData.case M) (ControlEnvironment.case M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M) hR hS
  intro A B a b e η hr ha hb
  change le (denoteCase M ha) (denoteCase M hb)
  rw [denoteCase_arrow hR ha, denoteCase_arrow hR hb]
  exact compose_mono hR le_rfl hr

/-- The native iteration quotient validates its whole generated directed theory. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.iterModel_refines_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .iter R) :
    Validates (iterModel (ε := ε) (F := .iter) (R := R) hR trivial).toSeqData
      (ControlData.iter (iterModel (F := .iter) (R := R) hR trivial)) (Refines (ε := ε) .iter R) := by
  let M := iterModel (ε := ε) (F := .iter) (R := R) hR trivial
  apply validates_of_singleton M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) hR hS
  intro A B a b e η hr ha hb
  change le (denoteIter M ha) (denoteIter M hb)
  rw [denoteIter_arrow hR ha, denoteIter_arrow hR hb]
  exact compose_mono hR le_rfl hr

end Silmaril.Isotope.Refinement.Models.Syntactic
