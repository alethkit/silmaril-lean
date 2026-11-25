module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs

/-! # Replacing a source product slot by its two components -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ProductSplit

universe u v w
variable {τ : Type u} {Φ : Type v} {ε : Type w}

/-- Replace the selected slot with its first component and prepend the second. -/
abbrev splitCtx [Bot ε] (Γ : EffectCtx τ ε) (i : Nat) (A B : τ) : EffectCtx τ ε :=
  (B, ⊥) :: SumSplit.branchCtx Γ i A

def splitSubst (i : Nat) (j : Nat) : Expr Φ :=
  if j = i then .pair (.var (i + 1)) (.var 0) else .var (j + 1)

def split (i : Nat) (a : Expr Φ) : Expr Φ := a.subst (splitSubst i)

def rebuild (i : Nat) (a : Expr Φ) : Expr Φ :=
  .let₂ (.var i) ((split i a).wk (Expr.liftWk (SumSplit.toFront i)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.ProductSplit
