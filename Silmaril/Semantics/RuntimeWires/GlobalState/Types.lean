module

public import Silmaril.Semantics.RuntimeWires.GlobalState.Thms
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

@[expose] public section

namespace Silmaril.RuntimeWires.GlobalState

open CategoryTheory

universe u

/-- The Cartesian copy and discard operations on a state type. -/
noncomputable abbrev typeComon (X : Type u) : ComonObj (C := Type u) X :=
  ((cartesianComon (Type u)).obj X).comon

attribute [local instance] typeComon

/-- A concrete model of Definition 4.1. Reading copies the state into a value,
and writing replaces the runtime state with the supplied value. -/
noncomputable def ofType (X : Type u) :
    GlobalState (C := Type u) X X where
  get := ↾fun x => (x, x)
  put := ↾fun x => x.2
  get_get := rfl
  get_discard := rfl
  put_put := rfl
  get_put := rfl
  put_get := rfl

/-- The four diagrams of Proposition 4.3 can have distinct results. Here the
two updates are increment and doubling, starting from a shared state of two. -/
theorem four_distinct_results :
    let S := ofType Nat
    let f : Nat ⟶ Nat := ↾fun n => n + 1
    let g : Nat ⟶ Nat := ↾fun n => 2 * n
    [S.race g f 2, S.race f g 2, (S.update f ≫ S.update g) 2,
      (S.update g ≫ S.update f) 2].Nodup := by
  change [3, 4, 6, 5].Nodup
  decide

end Silmaril.RuntimeWires.GlobalState
