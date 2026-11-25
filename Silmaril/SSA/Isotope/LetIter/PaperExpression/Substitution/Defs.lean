module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs

/-! # Renaming and substitution of written SSA expressions

These definitions follow `Term.wk`, `Term.Subst.lift`, `Term.subst`
and `Term.subst0` in the pinned `imbrem/debruijn-ssa` source, revision
`316bd9a6511d165b5d1d0042956a72e0f5547091`. A binary binder uses two
applications of the unary lift.
-/

@[expose] public section

universe v

namespace Silmaril.Isotope.LetIter.PaperExpression.Expr

variable {Φ : Type v}

/-- Lift a renaming below one new binding. -/
def liftWk (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (ρ i).succ

/-- Rename the de Bruijn variables of a source expression. -/
def wk (ρ : Nat → Nat) : Expr Φ → Expr Φ
  | .var i => .var (ρ i)
  | .op f a => .op f (wk ρ a)
  | .let₁ a b => .let₁ (wk ρ a) (wk (liftWk ρ) b)
  | .pair a b => .pair (wk ρ a) (wk ρ b)
  | .unit => .unit
  | .let₂ a b => .let₂ (wk ρ a) (wk (liftWk (liftWk ρ)) b)
  | .inl a => .inl (wk ρ a)
  | .inr a => .inr (wk ρ a)
  | .case a l r => .case (wk ρ a) (wk (liftWk ρ) l) (wk (liftWk ρ) r)
  | .abort a => .abort (wk ρ a)

def wk0 (a : Expr Φ) : Expr Φ := a.wk Nat.succ

def wk1 (a : Expr Φ) : Expr Φ := a.wk (liftWk Nat.succ)

def wk2 (a : Expr Φ) : Expr Φ := a.wk (liftWk (liftWk Nat.succ))

/-- Keep the newest slot and weaken all substituted expressions past it. -/
def liftSubst (σ : Nat → Expr Φ) : Nat → Expr Φ
  | 0 => .var 0
  | i + 1 => (σ i).wk0

/-- Simultaneous capture-avoiding source substitution. -/
def subst (σ : Nat → Expr Φ) : Expr Φ → Expr Φ
  | .var i => σ i
  | .op f a => .op f (subst σ a)
  | .let₁ a b => .let₁ (subst σ a) (subst (liftSubst σ) b)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .unit => .unit
  | .let₂ a b => .let₂ (subst σ a) (subst (liftSubst (liftSubst σ)) b)
  | .inl a => .inl (subst σ a)
  | .inr a => .inr (subst σ a)
  | .case a l r => .case (subst σ a) (subst (liftSubst σ) l) (subst (liftSubst σ) r)
  | .abort a => .abort (subst σ a)

/-- Replace the newest variable and decrement every older variable. -/
def subst0 (a : Expr Φ) : Nat → Expr Φ
  | 0 => a
  | i + 1 => .var i

end Silmaril.Isotope.LetIter.PaperExpression.Expr
