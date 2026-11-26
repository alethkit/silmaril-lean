module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetTraversal

/-! # Reuse an address for a partial region rewrite -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

variable {Φ : Type v}

/-- If the action commutes with substitution, so does its use at any address. -/
theorem Site.rewriteAt_substVars (root : Region Φ → Option (Region Φ))
    (natural : ∀ r θ, root (r.substVars θ) = (root r).map (·.substVars θ))
    (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    site.rewriteAt root (r.substVars θ) = (site.rewriteAt root r).map (·.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetTraversal.rewriteAt_substVars root natural site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

/-- A guarded root equation lifts through all region addresses. -/
theorem Site.rewriteAt_guarded (root : Region Φ → Option (Region Φ))
    (sound : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s}, ValueBranches Γ r L → root r = some s →
      ValueBranches Γ s L ∧ Extension.Eqv Seed Γ r s L)
    (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hm : site.rewriteAt root r = some s) :
    ValueBranches Γ s L ∧ Extension.Eqv Seed Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetTraversal.rewriteAt_guarded root sound site hr hm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
