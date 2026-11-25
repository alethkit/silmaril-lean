module

public import Silmaril.SSA.Isotope.Refinement.Models.Syntactic.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Free categorical models of the written quantitative let family -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Interpretation

universe u w r

/-- No additional rewrites beyond the native equations and directed rules. -/
def emptyRewrites (τ : Type u) (Φ : Type w) : Relation τ Φ := fun _ _ _ _ => False

variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

omit [HasTy Φ (Ty α)] in
theorem emptyRewrites_renamingClosed :
    Relation.RenamingClosed (emptyRewrites (Ty α) Φ) := fun _ _ h => False.elim h

/-- The singleton-context quotient by the complete written refinement theory. -/
def freeSeqModel : SeqModel.{u,w,w,r} (Ty α) Φ ε :=
  Syntactic.seqModel (F := .seq) (R := emptyRewrites (Ty α) Φ) emptyRewrites_renamingClosed

/-- The singleton-context quotient by the complete written refinement theory. -/
def freeCaseModel : CaseModel.{u,w,w,r} (Ty α) Φ ε :=
  Syntactic.caseModel (F := .case) (R := emptyRewrites (Ty α) Φ) emptyRewrites_renamingClosed trivial

/-- The singleton-context quotient by the complete written refinement theory. -/
def freeIterModel : IterModel.{u,w,w,r} (Ty α) Φ ε :=
  Syntactic.iterModel (F := .iter) (R := emptyRewrites (Ty α) Φ) emptyRewrites_renamingClosed trivial

end Silmaril.Isotope.Refinement.Models.Interpretation
