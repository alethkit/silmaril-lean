module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.SeqInitial
public import Silmaril.SSA.Isotope.Refinement.Models.Soundness.Thms

/-! # Sequential interpretation from proved native soundness

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
def seqModelMapOfValidates (M : SeqModel.{u,w,w,r} (Ty α) Φ ε)
    (hv : Validates M.toSeqData (ControlData.seq M) R) (hR : R.RenamingClosed) :
    Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR ⟶ M :=
  seqModelMap M (seq_validates_refines M hv) hR

@[simp] theorem seqModelMapOfValidates_of_typing (M : SeqModel.{u,w,w,r} (Ty α) Φ ε)
    (hv : Validates M.toSeqData (ControlData.seq M) R) (hR : R.RenamingClosed)
    {A B : Ty α} {e : ε} {t : Term Φ 1} (d : HasType .seq (Syntactic.input A) e t B) :
    (seqModelMapOfValidates M hv hR).map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteSeq M d) :=
  seqModelMap_of_typing M (seq_validates_refines M hv) hR d

/-- Soundness discharges the interpretation premise in categorical initiality.
The remaining argument is validity of the concrete native model itself. -/
def seqIsInitialOfValidNative (hR : R.RenamingClosed)
    (hv : seqValidity (ε := ε) R (Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR)) :
    IsInitial (seqPresentedModel hR hv) :=
  seqIsInitialOfSoundness hR hv (fun M => seq_validates_refines M.obj M.property)

end Silmaril.Isotope.Refinement.Models.Interpretation
