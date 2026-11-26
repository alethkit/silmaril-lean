module

public import Silmaril.Semantics.Dataflow.FiniteHeight.Defs
public import Silmaril.Semantics.Dataflow.Iteration

public section

namespace Silmaril.Semantics.Dataflow.FiniteHeight.Proofs

variable {α : Type*} [PartialOrder α] [OrderBot α]

theorem solve_fixed (height : HeightBound α) (f : α →o α) :
    f (height.solve f) = height.solve f := by
  let x (n : Nat) := (f : α → α)^[n] ⊥
  have next (n : Nat) : x (n + 1) = f (x n) := Function.iterate_succ_apply' _ _ _
  have increasing : Monotone x := f.monotone.monotone_iterate_of_le_map bot_le
  have strict (n : Nat) (unstable : f (x n) ≠ x n) : x n < x (n + 1) :=
    lt_of_le_of_ne (increasing (Nat.le_succ n)) fun equal =>
      unstable ((next n).symm.trans equal.symm)
  have growth (n : Nat) (unstable : f (x n) ≠ x n) : n + 1 ≤ height.rank (x (n + 1)) := by
    induction n with
    | zero =>
      exact Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt (height.rank_strict (strict 0 unstable)))
    | succ n ih =>
      have previous : f (x n) ≠ x n := by
        intro fixed
        have same := (next n).trans fixed
        exact unstable ((congrArg f same).trans (fixed.trans same.symm))
      exact (Nat.succ_le_succ (ih previous)).trans
        (Nat.succ_le_of_lt (height.rank_strict (strict (n + 1) unstable)))
  by_contra unstable
  exact Nat.not_succ_le_self height.bound
    ((growth height.bound unstable).trans (height.rank_le _))

theorem iterate_le_of_prefixed (f : α →o α) {upper : α} (h : f upper ≤ upper) (n : Nat) :
    (f : α → α)^[n] ⊥ ≤ upper := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (f.monotone ih).trans h

theorem iterateUntilStable_eq_some [DecidableEq α] (height : HeightBound α) (f : α →o α) :
    iterateUntilStable f (height.bound + 1) ⊥ = some (height.solve f) := by
  have success := iterateUntilStable_isSome_of_isFixedPt (f : α → α) (solve_fixed height f)
  cases run : iterateUntilStable f (height.bound + 1) ⊥ with
  | none => simp [run] at success
  | some answer =>
    have fixed := iterateUntilStable_isFixedPt (f : α → α) run
    have answer_le : answer ≤ height.solve f := by
      obtain ⟨n, _, equal⟩ := iterateUntilStable_eq_iterate (f : α → α) run
      rw [equal]
      exact iterate_le_of_prefixed f (solve_fixed height f).le n
    exact congrArg some (le_antisymm answer_le (iterate_le_of_prefixed f fixed.le height.bound))

end Silmaril.Semantics.Dataflow.FiniteHeight.Proofs
