module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.SeqSound
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.CaseSound
public import Silmaril.SSA.Isotope.Refinement.Models.Syntactic.Defs

/-! # Initial categorical models of native rewrite presentations

The quotient term models are initial among categorical models validating the
primitive presentation. Native validity, rule soundness, interpretation, and
uniqueness are all proved; none is an additional axiom on target models.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory CategoryTheory.Limits
universe u w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- The quotiented sequential syntax is the initial model of every native
rewrite presentation stable under weakening and pure substitution. -/
def _root_.Silmaril.Proofs.SSA.Isotope.Refinement.seqIsInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .seq) :
    IsInitial (Syntactic.seqModelOf R) :=
  seqIsInitialOfValidNative R.renamingClosed
    (Syntactic.seqModel_validates R.renamingClosed R.pureSubstitutionClosed)


/-- The quotiented branching syntax is the initial model of the presentation. -/
def _root_.Silmaril.Proofs.SSA.Isotope.Refinement.caseIsInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .case) :
    IsInitial (Syntactic.caseModelOf R) :=
  caseIsInitialOfValidNative R.renamingClosed
    (Syntactic.caseModel_validates R.renamingClosed R.pureSubstitutionClosed)


end Silmaril.Isotope.Refinement.Models.Interpretation
