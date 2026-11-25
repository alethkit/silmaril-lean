module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

open scoped BigOperators

namespace Silmaril.RuntimeWires.ProgressiveGraph.OrderedKnots

/-- Normalized distance from the left knot, clamped to the unit interval. -/
noncomputable def fraction (a b x : ℝ) : ℝ :=
  max 0 (min 1 ((x - a) / (b - a)))

/-- Accumulated lengths in the target subdivision, with unit-slope tails. -/
noncomputable def transfer {n : ℕ} (a b : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  b 0 + min (x - a 0) 0 +
    (∑ i : Fin n, (b i.succ - b i.castSucc) * fraction (a i.castSucc) (a i.succ) x) +
    max (x - a (Fin.last n)) 0

end Silmaril.RuntimeWires.ProgressiveGraph.OrderedKnots
