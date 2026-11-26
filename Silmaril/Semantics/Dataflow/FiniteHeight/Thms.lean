module

public import Silmaril.Semantics.Dataflow.FiniteHeight.Defs
public import Silmaril.Semantics.Dataflow.Iteration
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
import Silmaril.Proofs.Semantics.Dataflow.FiniteHeight.Iteration

/-! Finite-height termination and leastness of optimistic iteration. -/

@[expose] public section

namespace Silmaril.Semantics.Dataflow.FiniteHeight

namespace HeightBound

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- Independent rank budgets add in the pointwise product order. -/
def prod (a : HeightBound α) (b : HeightBound β) : HeightBound (α × β) where
  rank x := a.rank x.1 + b.rank x.2
  bound := a.bound + b.bound
  rank_strict := fun _ _ h => (Prod.lt_iff.mp h).elim
    (fun ⟨first, second⟩ => Nat.add_lt_add_of_lt_of_le (a.rank_strict first) (b.rank_strict.monotone second))
    (fun ⟨first, second⟩ => Nat.add_lt_add_of_le_of_lt (a.rank_strict.monotone first) (b.rank_strict second))
  rank_le x := Nat.add_le_add (a.rank_le x.1) (b.rank_le x.2)

/-- The pointwise order on a finite assignment uses the sum of the coordinate
budgets, even when the value at an index ranges over an infinite type. -/
def pi {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ i, PartialOrder (L i)]
    (height : ∀ i, HeightBound (L i)) : HeightBound ((i : ι) → L i) where
  rank x := ∑ i, (height i).rank (x i)
  bound := ∑ i, (height i).bound
  rank_strict := fun _ _ h =>
    let ⟨le, i, strict⟩ := Pi.lt_def.mp h
    Finset.sum_lt_sum (fun j _ => (height j).rank_strict.monotone (le j))
      ⟨i, Finset.mem_univ _, (height i).rank_strict strict⟩
  rank_le x := Finset.sum_le_sum fun i _ => (height i).rank_le (x i)

/-- Finite sets ordered by inclusion have a cardinality budget. -/
def finset (ι : Type*) [Fintype ι] : HeightBound (Finset ι) where
  rank := Finset.card
  bound := Fintype.card ι
  rank_strict := fun _ _ less => Finset.card_lt_card less
  rank_le := Finset.card_le_univ

section Bottom

variable [OrderBot α] (height : HeightBound α) (f : α →o α)

/-- Any strict step at the proposed bound would yield too many strict ascents. -/
theorem solve_fixed : f (height.solve f) = height.solve f :=
  Proofs.solve_fixed height f

/-- Every pre-fixed point bounds the computed solution from above. -/
theorem solve_le_of_prefixed {upper : α} (h : f upper ≤ upper) : height.solve f ≤ upper :=
  Proofs.iterate_le_of_prefixed f h height.bound

theorem solve_isLeast : IsLeast {x | f x = x} (height.solve f) :=
  ⟨height.solve_fixed f, fun upper h => height.solve_le_of_prefixed f (show f upper = upper from h).le⟩

/-- The existing equality-checking loop needs an extra step to check the final
iterate. It then returns the same solution as fixed-budget iteration. -/
theorem iterateUntilStable_eq_some [DecidableEq α] :
    iterateUntilStable f (height.bound + 1) ⊥ = some (height.solve f) :=
  Proofs.iterateUntilStable_eq_some height f

end Bottom

/-- In the dissertation's descending order, bottom iteration on the dual
computes the greatest fixed point. -/
theorem solve_dual_isGreatest [OrderTop α] (height : HeightBound αᵒᵈ) (f : α →o α) :
    IsGreatest {x | f x = x} (OrderDual.ofDual (height.solve f.dual)) :=
  height.solve_isLeast f.dual

end HeightBound

/-- On a complete lattice the executable result agrees with Mathlib's lfp. -/
theorem HeightBound.solve_eq_lfp {α : Type*} [CompleteLattice α] (height : HeightBound α) (f : α →o α) :
    height.solve f = f.lfp :=
  iterate_eq_lfp_of_isFixedPt f (height.solve_fixed f)

end Silmaril.Semantics.Dataflow.FiniteHeight
