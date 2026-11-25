module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs

/-! # Specializing a pure unit input slot -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}

/-- Delete the chosen slot, retaining all other slots in their original order. -/
abbrev eraseCtx (Γ : EffectCtx τ ε) (i : Nat) : EffectCtx τ ε := Γ.eraseIdx i

/-- Rename a slot in the smaller context into the original context. -/
def insertIndex (i j : Nat) : Nat := if j < i then j else j + 1

/-- Replace the chosen variable by unit and reindex the retained variables. -/
def unitSubst (i j : Nat) : Expr Φ :=
  if j = i then .unit else .var (if j < i then j else j - 1)

def specializeUnit (i : Nat) (a : Expr Φ) : Expr Φ := a.subst (unitSubst i)

def rebuildUnit (i : Nat) (a : Expr Φ) : Expr Φ :=
  (specializeUnit i a).wk (insertIndex i)

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot
