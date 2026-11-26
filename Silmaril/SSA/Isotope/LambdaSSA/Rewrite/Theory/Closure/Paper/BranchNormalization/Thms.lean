module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchNormalization

/-! # Typed branch binding respects the Paper rewrite relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Bind each branch argument once on both sides of an arbitrary typed Paper equation. -/
theorem Eqv.bindBranchArguments (h : Eqv Γ r s L) :
    Eqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchNormalization.paper_congr h

/-- Interpret normalized endpoints in a target extension. Only the new seed cases
need to be supplied by the caller. -/
theorem Extension.Eqv.bindBranchArguments_into
    {Seed Target : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (h : Extension.Eqv Seed Γ r s L)
    (map : ∀ {Γ r s L}, Seed Γ r s L → Extension.Eqv Target Γ r.bindBranchArguments s.bindBranchArguments L) :
    Extension.Eqv Target Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchNormalization.Extension.congr_into h map

/-- The same normalization respects a contextual extension whose seed has guarded endpoints. -/
theorem Extension.Eqv.bindBranchArguments_of_guardedSeed
    {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (guarded : ∀ {Γ r s L}, Seed Γ r s L → ValueBranches Γ r L ∧ ValueBranches Γ s L)
    (h : Extension.Eqv Seed Γ r s L) : Extension.Eqv Seed Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BranchNormalization.Extension.congr_of_guardedSeed guarded h

end Silmaril.Isotope.LambdaSSA.Region.Paper
