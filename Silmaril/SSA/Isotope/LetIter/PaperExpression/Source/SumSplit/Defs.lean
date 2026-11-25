module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs

/-! # Specializing one source context slot by a coproduct injection -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}

/-- Replace slot i in place. All old numerical indices are retained. -/
abbrev branchCtx [Bot ε] (Γ : EffectCtx τ ε) (i : Nat) (X : τ) : EffectCtx τ ε :=
  Γ.set i (X, ⊥)

/-- Change just one substitution image, preserving the numerical indices of
the other variables. -/
def replaceVar (i : Nat) (p : Expr Φ) (j : Nat) : Expr Φ :=
  if j = i then p else .var j

def left (i : Nat) (a : Expr Φ) : Expr Φ := a.subst (replaceVar i (.inl (.var i)))
def right (i : Nat) (a : Expr Φ) : Expr Φ := a.subst (replaceVar i (.inr (.var i)))

def toFront (i j : Nat) : Nat := if j = i then 0 else j + 1

def rebuild (i : Nat) (a : Expr Φ) : Expr Φ :=
  .case (.var i) ((left i a).wk (toFront i)) ((right i a).wk (toFront i))

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit
