module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # The standalone binary-let binding step -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.BinaryLetBind

open Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)

universe u v

/-- Bind the scrutinee once, then destructure that variable. -/
def rebound {Φ : Type v} (a : Tm Φ) (r : Region Φ) : Region Φ :=
  .let₁ a (.let₂ (.var 0) (r.renameVars (lift (lift Nat.succ))))

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}
  {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ}

theorem rebound_typed (ha : Tm.HasType Γ a (Silmaril.product A B))
    (hr : Region.HasType (B :: A :: Γ) r L) :
    Region.HasType Γ (rebound a r) L :=
  .let₁ ha (.let₂ (.var (i := 0) rfl)
    (hr.renameVars (((Ren.wk Γ (Silmaril.product A B)).lift A).lift B)))

/-- The region form of Figure 19's `let₂-bind` rule in
Ghalayini and Krishnaswami, *The Denotational Semantics of SSA*,
arXiv:2411.09347v2. The outer unary let evaluates the scrutinee once. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | bind {A B : τ} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {r : Region Φ}
      (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : HasType (B :: A :: Γ) r L) :
      Step Γ (.let₂ a r) (rebound a r) L

theorem Step.typed {s : Region Φ} (h : Step Γ r s L) : HasType Γ r L ∧ HasType Γ s L := by
  cases h with
  | bind ha hr => exact ⟨.let₂ ha hr, rebound_typed ha hr⟩

end Silmaril.Isotope.LambdaSSA.Region.BinaryLetBind
