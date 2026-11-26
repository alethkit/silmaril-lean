module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (StepsNWithin step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (entry model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)

private def increment : Profile := ⟨.add, 7, .eq⟩

-- This graph adds and takes the backedge on equality. The feedback changes 5 to 7.
example : recognize increment.graph = some increment := by cbv
example : recognize countdown.graph = some countdown := by cbv

private def mem : Memory := Memory.ofList 4 [29, 71, 53, 11]

private theorem lowers : lower increment.graph = some increment.lower := by
  cbv

private def carried (old : Word) : Tuple (Val model.value) [.value word] := .cons old .nil

private theorem sourceReturn :
    increment.graph.ReturnsAfter model (entry 5 2) 1
      (increment.graph.initial model (entry 5 2)) (7 : Word) :=
  .backedge (next := carried 7) (by cbv) (.exit (by cbv))

example : increment.lower.oracle 0 [5, 2] mem [7] mem :=
  (lower_returns_iff lowers 5 2 mem mem [7]).mpr ⟨7, ⟨1, sourceReturn⟩, rfl, rfl⟩

example :
    ∃ start finish, increment.lower.start 0 [5, 2] mem = some start ∧
      StepsNWithin increment.lower [] 9 start finish ∧
      step increment.lower finish = .returned [7] mem :=
  (lower_stepsN_iff lowers 5 2 mem mem [7] 1).mpr ⟨7, sourceReturn, rfl, rfl⟩

example : (increment.lower.runMain 9 0 [5, 2] mem).returnedValues? = none := by cbv
example : increment.lower.runMain 10 0 [5, 2] mem = .returned [7] mem := by cbv

/-- Changing an operand to a same-typed producer passes source typing. The
matcher must reject feedback from the limit instead of the update. -/
private def wrongFeedback : WordLoop :=
  { increment.graph with
    phiInputs
      | .entry => .cons (.arg .head) .nil
      | .backedge => .cons (.output (1 : Fin 3) .head) .nil }

example : lower wrongFeedback = none := by cbv

/-- Constants are valid word producers, but are admissible only at the limit
position in this schedule. -/
private def wrongUpdate : WordLoop :=
  { increment.graph with
    header :=
      match increment.graph.header with
      | .cons _ _ rest => .cons (.const 7) .nil rest }

example : lower wrongUpdate = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked
