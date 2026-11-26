module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Composition.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Guarded.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizationCongruence
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizationSubstitution

/-! # Transport of native branch binding under substitution and renaming -/

public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {Φ : Type v}

theorem bindBranchArguments_substVars (r : Region Φ) (σ : Nat → Tm Φ) :
    (r.substVars σ).bindBranchArguments = r.bindBranchArguments.substVars σ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindBranchArguments_substVars r σ

theorem bindBranchArguments_renameLabels (r : Region Φ) (ρ : Nat → Nat) :
    (r.renameLabels ρ).bindBranchArguments = r.bindBranchArguments.renameLabels ρ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindBranchArguments_renameLabels r ρ

/-- Binding branch arguments commutes with weakening captured variables. -/
theorem bindBranchArguments_liftLSubstVars (σ : Nat → Region Φ) :
    (fun i => (liftLSubstVars σ i).bindBranchArguments) =
      liftLSubstVars (fun i => (σ i).bindBranchArguments) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.normalizeLiftVars σ

end Silmaril.Isotope.LambdaSSA.Region
