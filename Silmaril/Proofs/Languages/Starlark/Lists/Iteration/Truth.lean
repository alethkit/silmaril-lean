module

public import Silmaril.Languages.Starlark.Lists.Iteration.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Iteration

open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

theorem projectCell_finishState {α : Type} (address : Address) (project : Contents → Option α)
    (s : State) : finishState (projectCell address project s) = s := by
  simp only [projectCell, bind, EStateM.bind, getCell]
  cases hs : s.heap[address]? with
  | none => rfl
  | some cell => dsimp only; cases project cell.contents <;> rfl

theorem map_finishState {α β : Type} (action : Meaning α) (f : α → β) (s : State) :
    finishState ((f <$> action) s) = finishState (action s) := by
  simp only [Functor.map, EStateM.map]
  cases action s <;> rfl

theorem truth_finishState (value : Value) (s : State) :
    finishState (truth value s) = s := by
  cases value with
  | list | tuple | dict =>
    rw [truth, map_finishState]
    exact projectCell_finishState _ _ s
  | _ => rfl

end Silmaril.Proofs.Languages.Starlark.Lists.Iteration
