module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Defs
import all Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # Constructor substitution in guarded regions -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Substitution by constructor values preserves guarded branches. -/
theorem ValueBranches.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    ValueBranches Δ (r.substVars θ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueBranches_substVars hr hθ

end Silmaril.Isotope.LambdaSSA.Region
