module

public import Silmaril.SSA.Isotope.Refinement.Models.Syntactic.Defs
public import Silmaril.SSA.Isotope.Refinement.Models.Soundness.Thms
import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.OrderedInterpretation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Reification
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseReification

/-! # Categorical completeness for native arrow judgments

These statements concern the singleton input judgments underlying the actual
categorical homs. Soundness applies in every model of a rewrite presentation;
the converse tests its concrete native quotient and uses proved reification.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation
universe u w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Sequential refinement is exactly the inequality valid in every categorical
model of the presentation, on native single-input arrows. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.seq_refines_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .seq (Syntactic.input A) e a B)
    (hb : HasType .seq (Syntactic.input A) η b B) :
    Refines (ε := ε) .seq R.rel (Syntactic.input A) a b B ↔
      ∀ M : SeqModelsOf.{u,w,r,w} (ε := ε) R.rel,
        M.obj.le (denoteSeq M.obj ha) (denoteSeq M.obj hb) := by
  constructor
  · intro h M
    exact seq_validates_refines M.obj M.property h ha hb
  · intro h
    have ht := h (Syntactic.seqModelOf R)
    change Syntactic.le (denoteSeq (Syntactic.seqModel R.renamingClosed) ha)
      (denoteSeq (Syntactic.seqModel R.renamingClosed) hb) at ht
    have hp := Syntactic.compose_mono R.renamingClosed
      (a := Syntactic.leftUnitInv A) le_rfl ht
    rw [Syntactic.denoteSeq_reify, Syntactic.denoteSeq_reify] at hp
    exact hp

/-- Mutual sequential refinement is exactly equality in every categorical model. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.seq_equates_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .seq (Syntactic.input A) e a B)
    (hb : HasType .seq (Syntactic.input A) η b B) :
    Equates (ε := ε) .seq R.rel (Syntactic.input A) a b B ↔
      ∀ M : SeqModelsOf.{u,w,r,w} (ε := ε) R.rel,
        denoteSeq M.obj ha = denoteSeq M.obj hb := by
  constructor
  · intro h M
    let := M.obj.toSeqData.homOrder
    exact le_antisymm
      ((Silmaril.Proofs.SSA.Isotope.Refinement.seq_refines_iff_models R ha hb).mp h.1 M)
      ((Silmaril.Proofs.SSA.Isotope.Refinement.seq_refines_iff_models R hb ha).mp h.2 M)
  · intro h
    exact ⟨(Silmaril.Proofs.SSA.Isotope.Refinement.seq_refines_iff_models R ha hb).mpr (fun M =>
      h M ▸ M.obj.toSeqData.le_refl _),
      (Silmaril.Proofs.SSA.Isotope.Refinement.seq_refines_iff_models R hb ha).mpr (fun M =>
        h M ▸ M.obj.toSeqData.le_refl _)⟩

/-- Branching refinement is exactly the inequality valid in all distributive
categorical models of the presentation. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.case_refines_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .case (Syntactic.input A) e a B)
    (hb : HasType .case (Syntactic.input A) η b B) :
    Refines (ε := ε) .case R.rel (Syntactic.input A) a b B ↔
      ∀ M : CaseModelsOf.{u,w,r,w} (ε := ε) R.rel,
        M.obj.le (denoteCase M.obj ha) (denoteCase M.obj hb) := by
  constructor
  · intro h M
    exact case_validates_refines M.obj M.property h ha hb
  · intro h
    have ht := h (Syntactic.caseModelOf R)
    change Syntactic.le (denoteCase (Syntactic.caseModel (F := .case) R.renamingClosed trivial) ha)
      (denoteCase (Syntactic.caseModel (F := .case) R.renamingClosed trivial) hb) at ht
    have hp := Syntactic.compose_mono R.renamingClosed
      (a := Syntactic.leftUnitInv A) le_rfl ht
    rw [Syntactic.denoteCase_reify, Syntactic.denoteCase_reify] at hp
    exact hp

/-- Mutual branching refinement is exactly equality in all distributive models. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.case_equates_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .case (Syntactic.input A) e a B)
    (hb : HasType .case (Syntactic.input A) η b B) :
    Equates (ε := ε) .case R.rel (Syntactic.input A) a b B ↔
      ∀ M : CaseModelsOf.{u,w,r,w} (ε := ε) R.rel,
        denoteCase M.obj ha = denoteCase M.obj hb := by
  constructor
  · intro h M
    let := M.obj.toSeqData.homOrder
    exact le_antisymm
      ((Silmaril.Proofs.SSA.Isotope.Refinement.case_refines_iff_models R ha hb).mp h.1 M)
      ((Silmaril.Proofs.SSA.Isotope.Refinement.case_refines_iff_models R hb ha).mp h.2 M)
  · intro h
    exact ⟨(Silmaril.Proofs.SSA.Isotope.Refinement.case_refines_iff_models R ha hb).mpr (fun M =>
      h M ▸ M.obj.toSeqData.le_refl _),
      (Silmaril.Proofs.SSA.Isotope.Refinement.case_refines_iff_models R hb ha).mpr (fun M =>
        h M ▸ M.obj.toSeqData.le_refl _)⟩

end Silmaril.Isotope.Refinement.Models.Interpretation
