module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.IterSound
public import Silmaril.SSA.Isotope.Refinement.Models.Syntactic.Defs

/-! # The initial iterative model of a native rewrite presentation

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

/-- The quotiented iterative syntax is the initial model of the presentation. -/
def _root_.Silmaril.Proofs.SSA.Isotope.Refinement.iterIsInitial (R : RewriteSystem (τ := Ty α) (Φ := Φ) (ε := ε) .iter) :
    IsInitial (Syntactic.iterModelOf R) :=
  iterIsInitialOfValidNative R.renamingClosed
    (Syntactic.iterModel_validates R.renamingClosed R.pureSubstitutionClosed)


end Silmaril.Isotope.Refinement.Models.Interpretation
