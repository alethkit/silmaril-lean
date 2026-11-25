module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Substitution

/-! # Unary β normalization and changes of context -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn

open CfgEta.TypeCategory (returnRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}
  {Γ Δ : VCtx τ} {t c : Tm Φ} {D : τ}

/-- Typed constructor substitution acts on both the source and its normal form. -/
theorem BetaNormalizes.subst (h : BetaNormalizes Γ t c D) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    BetaNormalizes Δ (t.subst θ) (c.subst θ) D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.subst h hθ

theorem BetaNormalizes.rename (h : BetaNormalizes Γ t c D) {ρ : Nat → Nat}
    (hρ : Ren Γ Δ ρ) : BetaNormalizes Δ (t.rename ρ) (c.rename ρ) D := by
  simpa only [Tm.rename_eq_subst] using h.subst (θ := Tm.var ∘ ρ) (fun _ _ hi => .var (hρ hi))

variable [HasTy Φ τ]

/-- Lower the substituted expression afresh, including the case where a variable
is replaced by a compound constructor value. -/
theorem BetaNormalizes.returnRegion_subst_eq_branch (h : BetaNormalizes Γ t c D)
    {θ : Nat → Tm Φ} (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Paper.Eqv Δ (returnRegion (t.subst θ)) (.br 0 (c.subst θ)) [D] :=
  (h.subst hθ).returnRegion_eq_branch

/-- Substitution of a lowered return agrees with lowering the substituted expression. -/
theorem BetaNormalizes.returnRegion_subst_transport (h : BetaNormalizes Γ t c D)
    {θ : Nat → Tm Φ} (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Paper.Eqv Δ ((returnRegion t).substVars θ) (returnRegion (t.subst θ)) [D] :=
  (h.returnRegion_eq_branch.substVars hθ).trans (h.returnRegion_subst_eq_branch hθ).symm

theorem BetaNormalizes.returnRegion_rename_eq_branch (h : BetaNormalizes Γ t c D)
    {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    Paper.Eqv Δ (returnRegion (t.rename ρ)) (.br 0 (c.rename ρ)) [D] :=
  (h.rename hρ).returnRegion_eq_branch

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn
