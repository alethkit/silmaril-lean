module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Witness.Defs

/-! # Different solutions for the two weighted networks -/

public section

namespace Silmaril.Calco2019.CounterSemiring

/-- Identifying the two states preserves the one-step equation. The
recursive coefficient is the sum of both labelled outgoing transitions. -/
theorem alternatingLoop_collapse (u : Bool) (y : Unit ⊕ Unit) :
    (match y with
      | .inl b => alternatingLoop u (.inl b)
      | .inr _ => ∑ v : Bool, alternatingLoop u (.inr v)) = singleLoop () y := by
  cases u <;> cases y <;> decide +revert

theorem singleLoop_solution : networkDagger singleLoop () () = .overflow := by decide

theorem alternatingLoop_solution (u : Bool) : networkDagger alternatingLoop u () = .both := by
  cases u <;> decide

/-- Finite elimination distinguishes the two-state cycle from its collapse
to one state, despite matching weights on exits and individual steps. -/
theorem network_two_cycle_counterexample (u : Bool) :
    networkDagger alternatingLoop u () ≠ networkDagger singleLoop () () := by
  rw [alternatingLoop_solution, singleLoop_solution]
  decide

end Silmaril.Calco2019.CounterSemiring
