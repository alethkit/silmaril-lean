module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Distributivity
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SeqModel
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Control

/-! # The native categorical case structure -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} (hR : R.RenamingClosed) (cap : F.HasCase)

theorem chosenCoproducts_distributor (A B C : τ) :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (ε := ε) (F := F) (R := R) hR
    (chosenCoproducts (ε := ε) (F := F) (R := R) hR cap).distributor A B C = distributor (ε := ε) (F := F) (R := R) cap A B C := rfl

/-- Chosen coproducts are enriched and distributive in every fragment supporting case. -/
theorem typeCaseCategory :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (ε := ε) (F := F) (R := R) hR
    letI := typeSymmetric (ε := ε) (F := F) (R := R) hR
    letI := typeHomOrder (ε := ε) (F := F) (R := R) hR
    CaseCategory τ ε (typeEffects (ε := ε) (F := F) (R := R) hR) (chosenCoproducts (ε := ε) (F := F) (R := R) hR cap) := by
  let := category (ε := ε) F R hR
  let := typePremonoidal (ε := ε) (F := F) (R := R) hR
  let := typeSymmetric (ε := ε) (F := F) (R := R) hR
  let := typeHomOrder (ε := ε) (F := F) (R := R) hR
  refine {
    inl := inl_pure cap
    inr := inr_pure cap
    initial := abort_pure cap
    desc := fun hf hg => desc_effect hR cap hf hg
    desc_mono := fun hf hg => desc_mono hR cap hf hg
    distributor_isIso := ?_
    distributor_inv := ?_ }
  · intro A B C
    exact ⟨⟨distributorInv (ε := ε) (F := F) (R := R) cap A B C,
      distributor_distributorInv hR cap A B C, distributorInv_distributor hR cap A B C⟩⟩
  · intro A B C
    let : IsIso ((chosenCoproducts (ε := ε) (F := F) (R := R) hR cap).distributor A B C) :=
      ⟨⟨distributorInv cap A B C, distributor_distributorInv hR cap A B C,
        distributorInv_distributor hR cap A B C⟩⟩
    have hi : inv ((chosenCoproducts (ε := ε) (F := F) (R := R) hR cap).distributor A B C) = distributorInv cap A B C :=
      IsIso.inv_eq_of_hom_inv_id (distributor_distributorInv hR cap A B C)
    rw [hi]
    exact distributorInv_pure cap A B C

/-- The native sequential model carries its chosen, distributive case operations. -/
def caseData : CaseData τ Φ ε where
  toSeqModel := seqModel (ε := ε) (F := F) (R := R) hR
  coproducts := chosenCoproducts (ε := ε) (F := F) (R := R) hR cap
  sum_obj _ _ := rfl
  initial_obj := rfl
  caseLaws := typeCaseCategory hR cap

@[simp] theorem caseData_inl (A B : τ) :
    (caseData (ε := ε) (F := F) (R := R) hR cap).inl A B = inl (R := R) cap A B := by
  change compose hR (inl cap A B) (identity _) = _
  exact compose_identity hR _

@[simp] theorem caseData_inr (A B : τ) :
    (caseData (ε := ε) (F := F) (R := R) hR cap).inr A B = inr (R := R) cap A B := by
  change compose hR (inr cap A B) (identity _) = _
  exact compose_identity hR _

@[simp] theorem caseData_desc {A B C : τ} (f : Hom (ε := ε) F R A C) (g : Hom (ε := ε) F R B C) :
    (caseData hR cap).desc f g = desc hR cap f g := by
  change compose hR (identity _) (desc hR cap f g) = _
  exact identity_compose hR _

@[simp] theorem caseData_abort (A : τ) :
    (caseData (ε := ε) (F := F) (R := R) hR cap).abort A = abort (R := R) cap A := by
  change compose hR (identity _) (abort cap A) = _
  exact identity_compose hR _

end Silmaril.Isotope.Refinement.Models.Syntactic
