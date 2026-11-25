module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseActs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterModel

/-! # Native operations underlying categorical control interpretation

The shared constructor interface is explicitly the quotient syntax operations.
The native categorical case and iteration models have these same operations;
normalization removes only the chosen type-equality transports.
-/

@[expose] public section
noncomputable section
universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

def nativeControl (hR : R.RenamingClosed) : ControlData (seqData (ε := ε) (F := F) (R := R) hR) F where
  inl cap := inl cap
  inr cap := inr cap
  desc cap := desc hR cap
  abort cap := abort cap
  distribute cap := distributorInv cap
  iterate cap := iterate hR cap

theorem case_control_eq (hR : R.RenamingClosed) :
    ControlData.case (caseModel (ε := ε) (F := .case) (R := R) hR trivial) =
      nativeControl (F := .case) hR := by
  unfold ControlData.case ControlData.ofCase nativeControl
  congr 1
  · funext cap A B
    exact caseData_inl (ε := ε) (F := .case) (R := R) hR trivial A B
  · funext cap A B
    exact caseData_inr (ε := ε) (F := .case) (R := R) hR trivial A B
  · funext cap A B C f g
    exact caseData_desc (ε := ε) (F := .case) (R := R) hR trivial f g
  · funext cap A
    exact caseData_abort (ε := ε) (F := .case) (R := R) hR trivial A
  · funext cap D A B
    exact caseData_distribute (ε := ε) (F := .case) (R := R) hR trivial D A B
  · funext cap
    exact False.elim cap

theorem iter_control_eq (hR : R.RenamingClosed) :
    ControlData.iter (iterModel (ε := ε) (F := .iter) (R := R) hR trivial) =
      nativeControl (F := .iter) hR := by
  unfold ControlData.iter ControlData.ofCase nativeControl
  congr 1
  · funext cap A B
    exact caseData_inl (ε := ε) (F := .iter) (R := R) hR trivial A B
  · funext cap A B
    exact caseData_inr (ε := ε) (F := .iter) (R := R) hR trivial A B
  · funext cap A B C f g
    exact caseData_desc (ε := ε) (F := .iter) (R := R) hR trivial f g
  · funext cap A
    exact caseData_abort (ε := ε) (F := .iter) (R := R) hR trivial A
  · funext cap D A B
    exact caseData_distribute (ε := ε) (F := .iter) (R := R) hR trivial D A B
  · funext cap A B f
    exact iterModel_iterate (ε := ε) (F := .iter) (R := R) hR trivial f

end Silmaril.Isotope.Refinement.Models.Syntactic
