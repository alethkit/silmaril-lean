module

import Silmaril.Semantics.Dataflow.FiniteHeight.Cycle.Defs
import Mathlib.Data.Fintype.Fin

namespace Silmaril.Semantics.Dataflow.FiniteHeight

open Cycle

private theorem bottomStartsOptimistic : (⊥ : Fin 3 × Fin 3) = (0, 0) := rfl
private theorem firstRound : step (0, 0) = (1, 0) := rfl
private theorem secondRound : step (1, 0) = (1, 1) := rfl
private theorem finiteHeightBound : height.bound = 4 := rfl
private theorem solved : answer = (1, 1) := rfl

private theorem largerFixedPoint : step (2, 2) = (2, 2) := rfl

private theorem leastOfFixedPoints : IsLeast {x | step x = x} (1, 1) :=
  height.solve_isLeast step

private theorem tightEarlyExit :
    iterateUntilStable step 2 ⊥ = none ∧
      iterateUntilStable step 3 ⊥ = some (1, 1) :=
  ⟨rfl, rfl⟩

private theorem certifiedEarlyExit :
    iterateUntilStable step (height.bound + 1) ⊥ = some answer :=
  height.iterateUntilStable_eq_some step

private theorem mixedBudget :
    ((HeightBound.finset (Fin 2)).prod (HeightBound.pi fun _ : Fin 2 => coordinateHeight)).bound = 6 :=
  by decide

end Silmaril.Semantics.Dataflow.FiniteHeight
