module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationCategory

/-! # Binding constructor branch arguments in the native rewrite theory -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Binding an existing constructor branch argument preserves the guarded
region's native rewrite class. -/
theorem ValueBranches.bindBranchArguments_equiv {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) : SubstitutionEquiv Γ r r.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindBranchArguments_equiv hr

end Silmaril.Isotope.LambdaSSA.Region
