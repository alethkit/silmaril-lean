module

public import Mathlib.Order.BoundedOrder.Basic

/-! Flat constant facts in the optimistic bottom order. -/

@[expose] public section

namespace Silmaril.Semantics.Dataflow

/-- No evidence, one exact value, or an overdefined value. The order forgets
any order on the concrete carrier, so distinct constants are incomparable. -/
inductive Flat (α : Type*) where
  | bottom
  | constant (value : α)
  | overdefined
  deriving DecidableEq, Repr

namespace Flat

variable {α β γ : Type*}

def le : Flat α → Flat α → Prop
  | .bottom, _ => True
  | _, .overdefined => True
  | .constant a, .constant b => a = b
  | _, _ => False

instance : PartialOrder (Flat α) where
  le := le
  le_refl a := by cases a <;> simp [le]
  le_trans a b c ab bc := by cases a <;> cases b <;> cases c <;> simp_all [le]
  le_antisymm a b ab ba := by cases a <;> cases b <;> simp_all [le]

instance : OrderBot (Flat α) where
  bot := .bottom
  bot_le _ := trivial

instance : OrderTop (Flat α) where
  top := .overdefined
  le_top a := by cases a <;> trivial

/-- Membership in the concretization of a fact. -/
def Covers (fact : Flat α) (value : α) : Prop :=
  match fact with
  | .bottom => False
  | .constant exactValue => exactValue = value
  | .overdefined => True

def join [DecidableEq α] : Flat α → Flat α → Flat α
  | .bottom, b => b
  | a, .bottom => a
  | .constant a, .constant b => if a = b then .constant a else .overdefined
  | _, _ => .overdefined

def map (f : α → β) : Flat α → Flat β
  | .bottom => .bottom
  | .constant a => .constant (f a)
  | .overdefined => .overdefined

/-- An application waits for evidence about every operand. With evidence at
every operand, overdefinition propagates and all constants are evaluated. -/
def map₂ (f : α → β → γ) : Flat α → Flat β → Flat γ
  | .bottom, _ | _, .bottom => .bottom
  | .constant a, .constant b => .constant (f a b)
  | _, _ => .overdefined

def rank : Flat α → Nat
  | .bottom => 0
  | .constant _ => 1
  | .overdefined => 2

end Flat

end Silmaril.Semantics.Dataflow
