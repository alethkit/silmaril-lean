module

public import Silmaril.SSA.Isotope.Refinement.Models.Initiality.Defs
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.FreeSeq
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.FreeCase
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.FreeIter
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Presented
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.PresentedIter
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Completeness
import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.IterCompleteness

/-! # Categorical initiality and singleton-input completeness

The free models are initial over a fixed signature on the free types.
Presented models use a formed rewrite system closed under quantitative renaming
and native pure substitution. The completeness statements compare denotations
of native arrows with one input in the full subcategory of validating models.
-/

public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Interpretation

open Denotation CategoryTheory CategoryTheory.Limits

universe u w r

variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)]
variable {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Every categorical sequential model receives a unique structure-preserving
map from the actual native syntax quotient. No validity premise is required. -/
def freeSeqModelIsInitial : IsInitial (freeSeqModel (α := α) (Φ := Φ) (ε := ε)) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.freeSeqModelIsInitial

/-- Every categorical branching model receives a unique structure-preserving
map from the actual native syntax quotient. No validity premise is required. -/
def freeCaseModelIsInitial : IsInitial (freeCaseModel (α := α) (Φ := Φ) (ε := ε)) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.freeCaseModelIsInitial

/-- Every categorical iterative model receives a unique structure-preserving
map from the actual native syntax quotient. No validity premise is required. -/
def freeIterModelIsInitial : IsInitial (freeIterModel (α := α) (Φ := Φ) (ε := ε)) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.freeIterModelIsInitial

/-- The quotiented sequential syntax is the initial model of every native
rewrite presentation stable under weakening and pure substitution. -/
def seqIsInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq) :
    IsInitial (Syntactic.seqModelOf R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.seqIsInitial R

/-- The quotiented branching syntax is the initial model of the presentation. -/
def caseIsInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case) :
    IsInitial (Syntactic.caseModelOf R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.caseIsInitial R

/-- The quotiented iterative syntax is the initial model of the presentation. -/
def iterIsInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter) :
    IsInitial (Syntactic.iterModelOf R) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.iterIsInitial R

/-- Existence of an initial object is witnessed by the concrete syntax quotient. -/
theorem seqHasInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq) :
    HasInitial (SeqModelsOf.{u,w,r,w} (ε := ε) R.rel) :=
  (seqIsInitial R).hasInitial

theorem caseHasInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case) :
    HasInitial (CaseModelsOf.{u,w,r,w} (ε := ε) R.rel) :=
  (caseIsInitial R).hasInitial

/-- The concrete syntax quotient witnesses existence of an initial model. -/
theorem iterHasInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter) :
    HasInitial (IterModelsOf.{u,w,r,w} (ε := ε) R.rel) :=
  (iterIsInitial R).hasInitial

/-- The unique arrow evaluates a representative by its categorical denotation. -/
@[simp] theorem seqIsInitial_to_of_typing
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq)
    (M : SeqModelsOf.{u,w,r,w} (ε := ε) R.rel)
    {A B : Ty α} {e : ε} {t : Term Φ 1} (d : HasType .seq (Syntactic.input A) e t B) :
    ((seqIsInitial R).to M).hom.map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.obj.compose (M.obj.leftUnitorInv A) (denoteSeq M.obj d) :=
  Syntactic.modelMap_ofArrow R.renamingClosed ((seqIsInitial R).to M).hom d

@[simp] theorem caseIsInitial_to_of_typing
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case)
    (M : CaseModelsOf.{u,w,r,w} (ε := ε) R.rel)
    {A B : Ty α} {e : ε} {t : Term Φ 1} (d : HasType .case (Syntactic.input A) e t B) :
    ((caseIsInitial R).to M).hom.map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.obj.compose (M.obj.leftUnitorInv A) (denoteCase M.obj d) :=
  Syntactic.caseModelMap_ofArrow R.renamingClosed ((caseIsInitial R).to M).hom d

@[simp] theorem iterIsInitial_to_of_typing
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter)
    (M : IterModelsOf.{u,w,r,w} (ε := ε) R.rel)
    {A B : Ty α} {e : ε} {t : Term Φ 1} (d : HasType .iter (Syntactic.input A) e t B) :
    ((iterIsInitial R).to M).hom.map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.obj.compose (M.obj.leftUnitorInv A) (denoteIter M.obj d) :=
  Syntactic.iterModelMap_ofArrow R.renamingClosed ((iterIsInitial R).to M).hom d

/-- Sequential refinement is exactly the inequality valid in every categorical
model of the presentation, on native single-input arrows. -/
theorem seq_refines_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .seq (Syntactic.input A) e a B)
    (hb : HasType .seq (Syntactic.input A) η b B) :
    Refines (ε := ε) .seq R.rel (Syntactic.input A) a b B ↔
      ∀ M : SeqModelsOf.{u,w,r,w} (ε := ε) R.rel,
        M.obj.le (denoteSeq M.obj ha) (denoteSeq M.obj hb) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.seq_refines_iff_models R ha hb

/-- Mutual sequential refinement is exactly equality in every categorical model. -/
theorem seq_equates_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .seq (Syntactic.input A) e a B)
    (hb : HasType .seq (Syntactic.input A) η b B) :
    Equates (ε := ε) .seq R.rel (Syntactic.input A) a b B ↔
      ∀ M : SeqModelsOf.{u,w,r,w} (ε := ε) R.rel,
        denoteSeq M.obj ha = denoteSeq M.obj hb :=
  Silmaril.Proofs.SSA.Isotope.Refinement.seq_equates_iff_models R ha hb

/-- Branching refinement is exactly the inequality valid in all distributive
categorical models of the presentation. -/
theorem case_refines_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .case (Syntactic.input A) e a B)
    (hb : HasType .case (Syntactic.input A) η b B) :
    Refines (ε := ε) .case R.rel (Syntactic.input A) a b B ↔
      ∀ M : CaseModelsOf.{u,w,r,w} (ε := ε) R.rel,
        M.obj.le (denoteCase M.obj ha) (denoteCase M.obj hb) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.case_refines_iff_models R ha hb

/-- Mutual branching refinement is exactly equality in all distributive models. -/
theorem case_equates_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .case (Syntactic.input A) e a B)
    (hb : HasType .case (Syntactic.input A) η b B) :
    Equates (ε := ε) .case R.rel (Syntactic.input A) a b B ↔
      ∀ M : CaseModelsOf.{u,w,r,w} (ε := ε) R.rel,
        denoteCase M.obj ha = denoteCase M.obj hb :=
  Silmaril.Proofs.SSA.Isotope.Refinement.case_equates_iff_models R ha hb

/-- Iterative refinement is exactly the inequality valid in all iterative
categorical models of the presentation. -/
theorem iter_refines_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .iter (Syntactic.input A) e a B)
    (hb : HasType .iter (Syntactic.input A) η b B) :
    Refines (ε := ε) .iter R.rel (Syntactic.input A) a b B ↔
      ∀ M : IterModelsOf.{u,w,r,w} (ε := ε) R.rel,
        M.obj.le (denoteIter M.obj ha) (denoteIter M.obj hb) :=
  Silmaril.Proofs.SSA.Isotope.Refinement.iter_refines_iff_models R ha hb

/-- Mutual iterative refinement is exactly equality in all iterative models. -/
theorem iter_equates_iff_models
    (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter)
    {A B : Ty α} {a b : Term Φ 1} {e η : ε}
    (ha : HasType .iter (Syntactic.input A) e a B)
    (hb : HasType .iter (Syntactic.input A) η b B) :
    Equates (ε := ε) .iter R.rel (Syntactic.input A) a b B ↔
      ∀ M : IterModelsOf.{u,w,r,w} (ε := ε) R.rel,
        denoteIter M.obj ha = denoteIter M.obj hb :=
  Silmaril.Proofs.SSA.Isotope.Refinement.iter_equates_iff_models R ha hb

end Silmaril.Isotope.Refinement.Models.Interpretation
