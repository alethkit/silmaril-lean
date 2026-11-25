module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}
  {Γ Δ : VCtx τ} {t c : Tm Φ} {D : τ}

theorem subst (h : BetaNormalizes Γ t c D) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    BetaNormalizes Δ (t.subst θ) (c.subst θ) D := by
  induction h generalizing Δ θ with
  | value hc => exact .value (hc.subst hθ)
  | @let₁ Γ a b c d A D ha hb iha ihb =>
    have liftTyping : ∀ ⦃i T⦄, At (A :: Γ) i T →
        Tm.BranchValue (A :: Δ) (Tm.liftSubst θ i) T := by
      intro i T hi
      cases i with
      | zero => cases Option.some.inj hi; exact .var rfl
      | succ i =>
        change Tm.BranchValue (A :: Δ) ((θ i).rename Nat.succ) T
        rw [Tm.rename_eq_subst]
        exact (hθ (show At Γ i T from hi)).subst (fun _ _ hx => .var (Ren.wk Δ A hx))
    have beta : (d.subst (Tm.singleSubst c)).subst θ =
        (d.subst (Tm.liftSubst θ)).subst (Tm.singleSubst (c.subst θ)) := by
      rw [Tm.subst_comp, Tm.subst_comp, Tm.singleSubst_comp]
    rw [beta]
    exact .let₁ (iha hθ) (ihb liftTyping)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta
