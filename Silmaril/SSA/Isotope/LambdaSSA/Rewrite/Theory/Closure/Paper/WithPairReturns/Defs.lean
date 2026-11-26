module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Defs

/-! # Opt-in left-to-right pair returns -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn.Beta.Constructors (pairSequence)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Forwarding a pair sequences the left computation, then the right in the
original context, and returns the two bound values. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | seq {Γ : VCtx τ} {A B : τ} {a b : Tm Φ}
      (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
      Step Γ (returnOnce (.pair a b)) (pairSequence a b) [product A B]

variable {ε : Type w} [HasEff Φ ε]

/-- Add just the pair-return rule to the named contextual return join. -/
abbrev JoinedStep (pe : ε) (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithCaseAndUnaryReturns.JoinedStep pe Γ r s L ∨ Step Γ r s L

section Typing

variable {Γ : VCtx τ} {A B : τ} {a b : Tm Φ}

theorem pairSequence_typed (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
    ValueBranches Γ (pairSequence a b) [product A B] :=
  .let₁ ha (.let₁ (hb.rename (Ren.wk Γ A)) (.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))

end Typing

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns
