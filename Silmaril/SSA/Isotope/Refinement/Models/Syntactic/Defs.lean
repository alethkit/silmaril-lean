module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SeqModel
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseModel
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterModel
public import Silmaril.SSA.Isotope.Refinement.Models.Defs
public import Silmaril.Raw.SSA.Isotope.Refinement.RewriteSystem
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Validity

/-! # Native categorical models of quantitative rewrite presentations

The native models have homs given by the mutual-refinement quotient of typed
singleton-input terms. The definitions import the native structure so that
the model homs reduce to the quotient carrier. Each model validates the
presentation in arbitrary quantitative contexts.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Syntactic
open Denotation
universe u v w
variable {α : Type u} [HasQuantity α]
variable {Φ : Type v} [HasTy Φ (Ty α)]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation (Ty α) Φ}

/-- The native sequential quotient validates its whole generated directed theory. -/
theorem seqModel_refines_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .seq R) :
    Validates (seqModel (ε := ε) (F := .seq) (R := R) hR).toSeqData
      (ControlData.seq (seqModel (F := .seq) (R := R) hR)) (Refines (ε := ε) .seq R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.seqModel_refines_validates hR hS

/-- The native case quotient validates its whole generated directed theory. -/
theorem caseModel_refines_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .case R) :
    Validates (caseModel (ε := ε) (F := .case) (R := R) hR trivial).toSeqData
      (ControlData.case (caseModel (F := .case) (R := R) hR trivial)) (Refines (ε := ε) .case R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.caseModel_refines_validates hR hS

/-- The native iteration quotient validates its whole generated directed theory. -/
theorem iterModel_refines_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .iter R) :
    Validates (iterModel (ε := ε) (F := .iter) (R := R) hR trivial).toSeqData
      (ControlData.iter (iterModel (F := .iter) (R := R) hR trivial)) (Refines (ε := ε) .iter R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.iterModel_refines_validates hR hS

/-- The sequential native model is an actual object of the presentation's model category. -/
theorem seqModel_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .seq R) :
    seqValidity R (seqModel (ε := ε) (F := .seq) (R := R) hR) := by
  intro n Γ a b A e η hr ha hb
  exact seqModel_refines_validates hR hS (.base hr ⟨ha.top⟩ ⟨hb.top⟩) ha hb

theorem caseModel_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .case R) :
    caseValidity R (caseModel (ε := ε) (F := .case) (R := R) hR trivial) := by
  intro n Γ a b A e η hr ha hb
  exact caseModel_refines_validates hR hS (.base hr ⟨ha.top⟩ ⟨hb.top⟩) ha hb

theorem iterModel_validates (hR : R.RenamingClosed)
    (hS : Relation.PureSubstitutionClosed (ε := ε) .iter R) :
    iterValidity R (iterModel (ε := ε) (F := .iter) (R := R) hR trivial) := by
  intro n Γ a b A e η hr ha hb
  exact iterModel_refines_validates hR hS (.base hr ⟨ha.top⟩ ⟨hb.top⟩) ha hb

/-- Package the actual native quotient with its proved presentation validity. -/
def seqModelOf (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq) : SeqModelsOf (ε := ε) R.rel :=
  ⟨seqModel (F := .seq) R.renamingClosed, seqModel_validates R.renamingClosed R.pureSubstitutionClosed⟩

def caseModelOf (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case) : CaseModelsOf (ε := ε) R.rel :=
  ⟨caseModel (F := .case) R.renamingClosed trivial, caseModel_validates R.renamingClosed R.pureSubstitutionClosed⟩

def iterModelOf (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter) : IterModelsOf (ε := ε) R.rel :=
  ⟨iterModel (F := .iter) R.renamingClosed trivial, iterModel_validates R.renamingClosed R.pureSubstitutionClosed⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
