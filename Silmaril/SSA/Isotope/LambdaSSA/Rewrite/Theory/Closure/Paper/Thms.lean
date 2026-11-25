module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Typing
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Contexts
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

/-! # Syntax and typed contexts of the opt-in λSSA relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem Eqv.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L) :
    HasType Γ r L ∧ HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.typed h

/-- Replace the sole outgoing continuation of a fixed typed producer. -/
theorem lsubst_singleton_congr {Γ : VCtx τ} {L : LCtx τ} {A : τ} {p r s : Region Φ}
    (hp : ValueBranches Γ p [A]) (h : Eqv (A :: Γ) r s L) :
    Eqv Γ (p.lsubst (fun _ => r)) (p.lsubst (fun _ => s)) L :=
  .lsubstCongr hp fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ h

/-- Reflexivity at an exact typing interface. -/
theorem Eqv.refl {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : HasType Γ r L) :
    Eqv Γ r r L :=
  .cfgEta (.native (.base (.refl hr)))

/-- Substitute pointwise equivalent outgoing continuations at value branches. -/
theorem lsubst_congr {Γ : VCtx τ} {L K : LCtx τ} {p : Region Φ} {σ υ : Nat → Region Φ}
    (hp : ValueBranches Γ p L) (h : Equivalent Γ L K σ υ) :
    Eqv Γ (p.lsubst σ) (p.lsubst υ) K :=
  .lsubstCongr hp h

/-- Rename the captured value variables at a common exact interface. -/
theorem Eqv.renameVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    Eqv Δ (r.renameVars ρ) (s.renameVars ρ) L := by
  simpa only [renameVars_eq_substVars] using h.substVars (θ := Tm.var ∘ ρ)
    (fun _ _ hi => Tm.BranchValue.var (hρ hi))

/-- Link arbitrary exactly typed equivalent producers and continuations.
The CFG evaluates an exit argument before entering its corresponding block. -/
theorem Eqv.linkExits {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {σ υ : Nat → Region Φ} (hs : Equivalent Γ L K σ υ) :
    Eqv Γ (r.linkExits L σ) (s.linkExits L υ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.linkExits h hs

end Silmaril.Isotope.LambdaSSA.Region.Paper
