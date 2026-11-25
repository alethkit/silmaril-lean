module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.SeqModel
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Control
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseModel

/-! # Categorical interpretation preserving coproducts -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable (M : CaseData.{u,v,w,r} τ Φ ε)
variable (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
variable (h : Sound M.toSeqData (ControlData.ofCase M F it) R) (cap : F.HasCase)

theorem map_inl (A B : τ) :
    map M.toSeqData (ControlData.ofCase M F it) h (Syntactic.inl cap A B) = M.inl A B :=
  (map_ofArrow M.toSeqData (ControlData.ofCase M F it) h _ (Syntactic.inlDeriv cap A B (⊤ : ε))).trans
    (denoteArrow_inlDeriv M it cap A B ⊤)

theorem map_inr (A B : τ) :
    map M.toSeqData (ControlData.ofCase M F it) h (Syntactic.inr cap A B) = M.inr A B :=
  (map_ofArrow M.toSeqData (ControlData.ofCase M F it) h _ (Syntactic.inrDeriv cap A B (⊤ : ε))).trans
    (denoteArrow_inrDeriv M it cap A B ⊤)

theorem map_abort (A : τ) :
    map M.toSeqData (ControlData.ofCase M F it) h (Syntactic.abort cap A) = M.abort A :=
  (map_ofArrow M.toSeqData (ControlData.ofCase M F it) h _ (Syntactic.abortDeriv cap A (⊤ : ε))).trans
    (denoteArrow_abortDeriv M it cap A ⊤)

theorem map_desc (hR : R.RenamingClosed) (N : ControlEnvironment (ControlData.ofCase M F it))
    {A B C : τ} (a : Syntactic.Hom (ε := ε) F R A C) (b : Syntactic.Hom (ε := ε) F R B C) :
    map M.toSeqData (ControlData.ofCase M F it) h (Syntactic.desc hR cap a b) =
      M.desc (map M.toSeqData (ControlData.ofCase M F it) h a) (map M.toSeqData (ControlData.ofCase M F it) h b) := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    obtain ⟨da⟩ := a.property
    obtain ⟨db⟩ := b.property
    exact (map_ofArrow M.toSeqData (ControlData.ofCase M F it) h (Syntactic.descArrow cap a b) (Syntactic.descDeriv cap da db)).trans
      ((denoteArrow_descDeriv M it N (Sound.coherent M.toSeqData (ControlData.ofCase M F it) h) cap da db).trans
        (congrArg₂ M.desc (map_ofArrow M.toSeqData (ControlData.ofCase M F it) h a da).symm
          (map_ofArrow M.toSeqData (ControlData.ofCase M F it) h b db).symm))

/-- Shared preservation of case structure for branching and iterative syntax. -/
def caseDataMap (M : CaseData.{u,w,w,r} τ Φ ε)
    (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
    (h : Sound M.toSeqData (ControlData.ofCase M F it) R) (hR : R.RenamingClosed) (cap : F.HasCase)
    (N : ControlEnvironment (ControlData.ofCase M F it)) (E : ControlEffects (ControlData.ofCase M F it)) :
    CaseData.HomMap (Syntactic.caseData (ε := ε) (F := F) (R := R) hR cap) M where
  toHomMap := seqDataMap M.toSeqModel (ControlData.ofCase M F it) h hR N E
  inl A B :=
    (congrArg (map M.toSeqData (ControlData.ofCase M F it) h)
      (Syntactic.caseData_inl (ε := ε) (F := F) (R := R) hR cap A B)).trans (map_inl M it h cap A B)
  inr A B :=
    (congrArg (map M.toSeqData (ControlData.ofCase M F it) h)
      (Syntactic.caseData_inr (ε := ε) (F := F) (R := R) hR cap A B)).trans (map_inr M it h cap A B)
  desc a b :=
    (congrArg (map M.toSeqData (ControlData.ofCase M F it) h)
      (Syntactic.caseData_desc (ε := ε) (F := F) (R := R) hR cap a b)).trans (map_desc M it h cap hR N a b)
  abort A :=
    (congrArg (map M.toSeqData (ControlData.ofCase M F it) h)
      (Syntactic.caseData_abort (ε := ε) (F := F) (R := R) hR cap A)).trans (map_abort M it h cap A)

/-- A genuine map of branching categorical models, given native soundness. -/
def caseModelMap (M : CaseModel.{u,w,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.case M) R) (hR : R.RenamingClosed) :
    Syntactic.caseModel (ε := ε) (F := .case) (R := R) hR trivial ⟶ M :=
  caseDataMap (F := .case) M.toCaseData (fun h => False.elim h) h hR trivial
    (ControlEnvironment.case M) (ControlEffects.case M)

@[simp] theorem caseModelMap_of_typing (M : CaseModel.{u,w,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.case M) R) (hR : R.RenamingClosed)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .case (Syntactic.input A) e t B) :
    (caseModelMap M h hR).map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteCase M d) :=
  map_of_typing M.toSeqData (ControlData.case M) h d

end Silmaril.Isotope.Refinement.Models.Interpretation
