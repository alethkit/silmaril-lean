module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyCoproducts

/-! # The native categorical case model -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The quotient model has distributive coproducts and compatible quantitative copy/discard. -/
def caseModel (hR : R.RenamingClosed) (cap : F.HasCase) : CaseModel τ Φ ε := by
  refine { toCaseData := caseData (ε := ε) (F := F) (R := R) hR cap
           discard_empty := ?_, copy_empty := ?_, discard_coprod := ?_, copy_coprod := ?_ }
  · intro h
    change (seqData (ε := ε) (F := F) (R := R) hR).discard Silmaril.empty h =
      (caseData hR cap).abort Silmaril.unit
    rw [seqData_discard, caseData_abort]
    exact discard_empty cap h
  · intro h
    change (seqData (ε := ε) (F := F) (R := R) hR).copy Silmaril.empty h =
      (caseData hR cap).abort (product Silmaril.empty Silmaril.empty)
    rw [seqData_copy, caseData_abort]
    exact copy_empty cap h
  · intro A B hA hB hAB
    change (seqData (ε := ε) (F := F) (R := R) hR).discard (coprod A B) hAB =
      (caseData hR cap).desc ((seqData hR).discard A hA) ((seqData hR).discard B hB)
    simp only [seqData_discard, caseData_desc]
    exact discard_coprod hR cap A B hA hB hAB
  · intro A B hA hB hAB
    change (seqData (ε := ε) (F := F) (R := R) hR).copy (coprod A B) hAB =
      (caseData hR cap).desc
        ((seqData hR).compose ((seqData hR).copy A hA)
          ((seqData hR).tensor ((caseData hR cap).inl A B) ((caseData hR cap).inl A B)))
        ((seqData hR).compose ((seqData hR).copy B hB)
          ((seqData hR).tensor ((caseData hR cap).inr A B) ((caseData hR cap).inr A B)))
    simp only [SeqData.tensor, seqData_copy, seqData_compose, seqData_right,
      seqData_left, caseData_desc, caseData_inl, caseData_inr]
    exact copy_coprod hR cap A B hA hB hAB

end Silmaril.Isotope.Refinement.Models.Syntactic
