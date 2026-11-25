module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.IterInitial
public import Silmaril.SSA.Isotope.Refinement.Models.Soundness.Thms

/-! # Iterative interpretation from proved native soundness

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
def iterModelMapOfValidates (M : IterModel.{u,w,w,r} (Ty α) Φ ε)
    (hv : Validates M.toSeqData (ControlData.iter M) R) (hR : R.RenamingClosed) :
    Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial ⟶ M :=
  iterModelMap M (iter_validates_refines M hv) hR

@[simp] theorem iterModelMapOfValidates_of_typing (M : IterModel.{u,w,w,r} (Ty α) Φ ε)
    (hv : Validates M.toSeqData (ControlData.iter M) R) (hR : R.RenamingClosed)
    {A B : Ty α} {e : ε} {t : Term Φ 1} (d : HasType .iter (Syntactic.input A) e t B) :
    (iterModelMapOfValidates M hv hR).map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteIter M d) :=
  iterModelMap_of_typing M (iter_validates_refines M hv) hR d

/-- Soundness discharges the interpretation premise in categorical initiality.
The remaining argument is validity of the concrete native model itself. -/
def iterIsInitialOfValidNative (hR : R.RenamingClosed)
    (hv : iterValidity (ε := ε) R (Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial)) :
    IsInitial (iterPresentedModel hR hv) :=
  iterIsInitialOfSoundness hR hv (fun M => iter_validates_refines M.obj M.property)

end Silmaril.Isotope.Refinement.Models.Interpretation
