module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ControlReification
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Naturality

/-! # Native case reification and uniqueness of categorical interpretation

The case quotient interprets every typing derivation as its own arrow.
Consequently actual structure-preserving model maps are unique, independently
of the separate soundness argument needed to construct such a map.
-/

@[expose] public section
noncomputable section
universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation τ Φ}

theorem denoteCase_acts (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (d : HasType .case Γ e t A) (hΓ : Γ.DefaultAnnotations) :
    Acts Γ (packTerm Γ) (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d) t := by
  unfold denoteCase
  rw [case_control_eq (ε := ε) (R := R) hR]
  apply denote_native_acts hR _ d hΓ
  intro n Γ Γl Γr a b A B cap
  exact False.elim cap

/-- Feeding the singleton packing map to native interpretation recovers the
original quotient arrow. -/
theorem denoteCase_reify (hR : R.RenamingClosed) {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType .case (input A) e t B) :
    compose (ε := ε) (F := .case) (R := R) hR (leftUnitInv A)
      (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d) =
      ofArrow (R := R) ⟨t, ⟨d.top⟩⟩ := by
  obtain ⟨r, hr, he⟩ := denoteCase_acts (R := R) hR d (input_default A)
  rw [← hr]
  apply Quotient.sound
  change Equates (ε := ε) .case R (input A)
    (composeArrow (leftUnitInvArrow A) r).val t B
  simpa only [composeArrow, composeTerm, leftUnitInvArrow, continuation_atIndex,
    input, packTerm_snoc_used, packTerm_nil, Tm.lift, Tm.rename, action] using he

/-- The interpretation itself is the original quotient arrow preceded by the
unitor that removes the packed empty-context unit. -/
theorem denoteCase_arrow (hR : R.RenamingClosed) {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType .case (input A) e t B) :
    denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d =
      compose (ε := ε) (F := .case) (R := R) hR (leftUnit A) (ofArrow (R := R) ⟨t, ⟨d.top⟩⟩) := by
  have h := congrArg (compose (ε := ε) (F := .case) (R := R) hR (leftUnit A)) (denoteCase_reify (R := R) hR d)
  rw [← compose_assoc (ε := ε) (F := .case) (R := R) hR
      (leftUnit A) (leftUnitInv A)
      (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d),
    leftUnit_leftUnitInv (ε := ε) (F := .case) (R := R) hR A] at h
  exact (identity_compose (ε := ε) (F := .case) (R := R) hR
    (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d)).symm.trans h


/-- Every structure-preserving model map agrees with interpretation on an
arbitrary typed representative. The initial unit is removed explicitly. -/
theorem caseModelMap_ofArrow (hR : R.RenamingClosed)
    {M : CaseModel.{u,v,v,w} τ Φ ε}
    (φ : caseModel (ε := ε) (F := .case) (R := R) hR trivial ⟶ M)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .case (input A) e t B) :
    φ.map (ofArrow (R := R) ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteCase M d) := by
  have hu := φ.leftUnitorInv A
  change φ.map ((seqData (ε := ε) (F := .case) (R := R) hR).leftUnitorInv A) = _ at hu
  rw [seqData_leftUnitorInv (ε := ε) (F := .case) (R := R) hR A] at hu
  calc
    _ = φ.map (compose (ε := ε) (F := .case) (R := R) hR (leftUnitInv A)
        (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d)) :=
      congrArg φ.map (denoteCase_reify (R := R) hR d).symm
    _ = M.compose (φ.map (leftUnitInv A))
        (φ.map (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d)) :=
      φ.compose (leftUnitInv A) (denoteCase (caseModel (ε := ε) (F := .case) (R := R) hR trivial) d)
    _ = _ := congrArg₂ M.compose hu (denoteCase_naturality φ d)

/-- Maps from the native case model are unique because their values on
all quotient representatives are fixed by the categorical operations. -/
theorem caseModelMap_unique (hR : R.RenamingClosed)
    {M : CaseModel.{u,v,v,w} τ Φ ε}
    (φ ψ : caseModel (ε := ε) (F := .case) (R := R) hR trivial ⟶ M) : φ = ψ := by
  apply CaseData.HomMap.ext
  apply SeqData.HomMap.ext
  intro A B a
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨d⟩ := a.property
    exact (caseModelMap_ofArrow hR φ d).trans (caseModelMap_ofArrow hR ψ d).symm

end Silmaril.Isotope.Refinement.Models.Syntactic
