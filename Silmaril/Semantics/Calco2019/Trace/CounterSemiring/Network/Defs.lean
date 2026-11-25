module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Elimination.Thms
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Algebra.Group.End

/-! # Finite feedback elimination on weighted networks -/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.CounterSemiring

/-- Weighted entries from an input or state to an output or state. -/
abbrev Network (A : Type u) (B : Type v) (U : Type w) := (A ⊕ U) → (B ⊕ U) → Scalar

variable {A : Type u} {B : Type v} {U : Type w}

/-- Update all entries by accounting for paths through the specified state. -/
def eliminateState (u : U) : Function.End (Network A B U) := fun f x y =>
  Scalar.eliminate (f x y) (f x (.inr u)) (f (.inr u) (.inr u)) (f (.inr u) y)

/-- Single-state updates commute, so a finite set can be eliminated
without selecting an enumeration. -/
theorem eliminateState_commute (u v : U) :
    Commute (eliminateState (A := A) (B := B) u) (eliminateState v) := by
  funext f x y
  exact (Scalar.eliminate_pair (f x y) (f x (.inr u)) (f x (.inr v))
    (f (.inr u) y) (f (.inr v) y) (f (.inr u) (.inr u)) (f (.inr u) (.inr v))
    (f (.inr v) (.inr u)) (f (.inr v) (.inr v))).symm

/-- Apply the scalar elimination update to the selected feedback states. -/
def eliminateStates (s : Finset U) : Function.End (Network A B U) :=
  s.noncommProd eliminateState (fun u _ v _ _ => eliminateState_commute u v)

theorem eliminateStates_insert [DecidableEq U] (s : Finset U) (u : U) (h : u ∉ s)
    (f : Network A B U) :
    eliminateStates (insert u s) f = eliminateState u (eliminateStates s f) :=
  congrArg (fun m : Function.End (Network A B U) => m f)
    (Finset.noncommProd_insert_of_notMem s u (eliminateState (A := A) (B := B)) _ h)

end Silmaril.Calco2019.CounterSemiring
