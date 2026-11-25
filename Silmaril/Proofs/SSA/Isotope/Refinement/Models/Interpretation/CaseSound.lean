module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.CaseInitial
public import Silmaril.SSA.Isotope.Refinement.Models.Soundness.Thms

/-! # Branching interpretation from proved native soundness

The only condition on the target model is validity of the specified primitive
rewrites. The full written refinement calculus is sound by the preceding
semantic metatheory, and therefore need not be assumed by the interpretation.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory CategoryTheory.Limits
universe u w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation (Ty α) Φ}

/-- The actual categorical interpretation into every model of the generators. -/
def caseModelMapOfValidates (M : CaseModel.{u,w,w,r} (Ty α) Φ ε)
    (hv : Validates M.toSeqData (ControlData.case M) R) (hR : R.RenamingClosed) :
    Syntactic.caseModel (ε := ε) (F := .case) (R := R) hR trivial ⟶ M :=
  caseModelMap M (case_validates_refines M hv) hR

@[simp] theorem caseModelMapOfValidates_of_typing (M : CaseModel.{u,w,w,r} (Ty α) Φ ε)
    (hv : Validates M.toSeqData (ControlData.case M) R) (hR : R.RenamingClosed)
    {A B : Ty α} {e : ε} {t : Term Φ 1} (d : HasType .case (Syntactic.input A) e t B) :
    (caseModelMapOfValidates M hv hR).map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteCase M d) :=
  caseModelMap_of_typing M (case_validates_refines M hv) hR d

/-- Soundness discharges the interpretation premise in categorical initiality.
The remaining argument is validity of the concrete native model itself. -/
def caseIsInitialOfValidNative (hR : R.RenamingClosed)
    (hv : caseValidity (ε := ε) R (Syntactic.caseModel (ε := ε) (F := .case) (R := R) hR trivial)) :
    IsInitial (casePresentedModel hR hv) :=
  caseIsInitialOfSoundness hR hv (fun M => case_validates_refines M.obj M.property)

end Silmaril.Isotope.Refinement.Models.Interpretation
