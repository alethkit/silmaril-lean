module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.CaseModel
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Iteration
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterModel

/-! # Categorical interpretation preserving iteration -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation τ Φ}

theorem map_iterate (M : IterModel.{u,v,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.iter M) R) (hR : R.RenamingClosed)
    {A B : τ} (a : Syntactic.Hom (ε := ε) .iter R A (coprod B A)) :
    map M.toSeqData (ControlData.iter M) h (Syntactic.iterate hR trivial a) =
      M.iterate (map M.toSeqData (ControlData.iter M) h a) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨da⟩ := a.property
    exact (map_ofArrow M.toSeqData (ControlData.iter M) h
      (Syntactic.iterateArrow trivial a) (Syntactic.iterateDeriv (F := .iter) trivial EffectSystem.iterable_top da)).trans
      ((denoteArrow_iterateDeriv M (Sound.coherent M.toSeqData (ControlData.iter M) h)
        EffectSystem.iterable_top da).trans
        (congrArg M.iterate (map_ofArrow M.toSeqData (ControlData.iter M) h a da).symm))

/-- A genuine map of iterative categorical models, given native soundness. -/
def iterModelMap (M : IterModel.{u,w,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.iter M) R) (hR : R.RenamingClosed) :
    Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial ⟶ M where
  toCaseHom := caseDataMap M.toCaseData (fun _ => M.iterate) h hR trivial
    (ControlEnvironment.iter M) (ControlEffects.iter M)
  iterate a :=
    (congrArg (map M.toSeqData (ControlData.iter M) h)
      (Syntactic.iterModel_iterate (ε := ε) (F := .iter) (R := R) hR trivial a)).trans
      (map_iterate M h hR a)

@[simp] theorem iterModelMap_of_typing (M : IterModel.{u,w,w,r} τ Φ ε)
    (h : Sound M.toSeqData (ControlData.iter M) R) (hR : R.RenamingClosed)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .iter (Syntactic.input A) e t B) :
    (iterModelMap M h hR).map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.compose (M.leftUnitorInv A) (denoteIter M d) :=
  map_of_typing M.toSeqData (ControlData.iter M) h d

end Silmaril.Isotope.Refinement.Models.Interpretation
