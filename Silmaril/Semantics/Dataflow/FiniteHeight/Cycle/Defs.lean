module

public import Silmaril.Semantics.Dataflow.FiniteHeight.Thms
public import Mathlib.Order.Fin.Basic

/-! Two mutually dependent equations on three-point chains. -/

@[expose] public section

namespace Silmaril.Semantics.Dataflow.FiniteHeight.Cycle

def coordinateHeight : HeightBound (Fin 3) where
  rank := Fin.val
  bound := 2
  rank_strict := fun _ _ less => less
  rank_le x := Nat.le_of_lt_succ x.isLt

def height : HeightBound (Fin 3 × Fin 3) := coordinateHeight.prod coordinateHeight

/-- The first coordinate reads the second and joins in the seed `1`.
The second reads the first. Each round reads the previous pair. -/
def step : (Fin 3 × Fin 3) →o (Fin 3 × Fin 3) where
  toFun facts := (max 1 facts.2, facts.1)
  monotone' _ _ le := ⟨max_le_max le_rfl le.2, le.1⟩

def answer : Fin 3 × Fin 3 := height.solve step

end Silmaril.Semantics.Dataflow.FiniteHeight.Cycle
