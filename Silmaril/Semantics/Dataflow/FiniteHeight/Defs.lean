module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Iterate

/-! Bounded bottom iteration in the order dual of optimistic meet iteration. -/

@[expose] public section

namespace Silmaril.Semantics.Dataflow.FiniteHeight

/-- A bounded rank increasing along every strict ascent. The bound counts
strict steps, and the carrier may have infinitely many incomparable values. -/
structure HeightBound (α : Type*) [PartialOrder α] where
  rank : α → Nat
  bound : Nat
  rank_strict : StrictMono rank
  rank_le : ∀ x, rank x ≤ bound

variable {α : Type*} [PartialOrder α] [OrderBot α]

/-- Apply the simultaneous transfer exactly the certified number of times,
starting from the optimistic bottom. -/
def HeightBound.solve (height : HeightBound α) (f : α →o α) : α :=
  (f : α → α)^[height.bound] ⊥

end Silmaril.Semantics.Dataflow.FiniteHeight
