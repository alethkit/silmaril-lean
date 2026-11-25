module

public import Silmaril.SSA.Isotope.Refinement.Models.Syntactic.Defs
public import Silmaril.SSA.Isotope.Refinement.Models.Soundness.Thms
import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.OrderedInterpretation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterReification

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

/-- Iterative refinement is exactly the inequality valid in all iterative
categorical models of the presentation. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.iter_refines_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .iter (Syntactic.input A) e a B)
    (hb : HasType .iter (Syntactic.input A) η b B) :
    Refines (ε := ε) .iter R.rel (Syntactic.input A) a b B ↔
      ∀ M : IterModelsOf.{u,w,r,w} (ε := ε) R.rel,
        M.obj.le (denoteIter M.obj ha) (denoteIter M.obj hb) := by
  constructor
  · intro h M
    exact iter_validates_refines M.obj M.property h ha hb
  · intro h
    have ht := h (Syntactic.iterModelOf R)
    change Syntactic.le (denoteIter (Syntactic.iterModel (F := .iter) R.renamingClosed trivial) ha)
      (denoteIter (Syntactic.iterModel (F := .iter) R.renamingClosed trivial) hb) at ht
    have hp := Syntactic.compose_mono R.renamingClosed
      (a := Syntactic.leftUnitInv A) le_rfl ht
    rw [Syntactic.denoteIter_reify, Syntactic.denoteIter_reify] at hp
    exact hp

/-- Mutual iterative refinement is exactly equality in all iterative models. -/
theorem _root_.Silmaril.Proofs.SSA.Isotope.Refinement.iter_equates_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .iter (Syntactic.input A) e a B)
    (hb : HasType .iter (Syntactic.input A) η b B) :
    Equates (ε := ε) .iter R.rel (Syntactic.input A) a b B ↔
      ∀ M : IterModelsOf.{u,w,r,w} (ε := ε) R.rel,
        denoteIter M.obj ha = denoteIter M.obj hb := by
  constructor
  · intro h M
    let := M.obj.toSeqData.homOrder
    exact le_antisymm
      ((Silmaril.Proofs.SSA.Isotope.Refinement.iter_refines_iff_models R ha hb).mp h.1 M)
      ((Silmaril.Proofs.SSA.Isotope.Refinement.iter_refines_iff_models R hb ha).mp h.2 M)
  · intro h
    exact ⟨(Silmaril.Proofs.SSA.Isotope.Refinement.iter_refines_iff_models R ha hb).mpr (fun M =>
      h M ▸ M.obj.toSeqData.le_refl _),
      (Silmaril.Proofs.SSA.Isotope.Refinement.iter_refines_iff_models R hb ha).mpr (fun M =>
        h M ▸ M.obj.toSeqData.le_refl _)⟩

end Silmaril.Isotope.Refinement.Models.Interpretation
