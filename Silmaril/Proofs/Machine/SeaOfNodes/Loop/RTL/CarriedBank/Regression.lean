module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (StepsNWithin step)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA (Inputs)

private def args (limit : Word) : Inputs Word := ⟨limit, 3, 1⟩

private def mem : Memory := Memory.ofList 4 [29, 71, 53, 11]

private theorem accepted : lowerChecked graph = some lower := by cbv

private theorem zero :
    graph.ReturnsAfter model (input (args 0)) 0 (graph.initial model (input (args 0))) (2 : Word) :=
  .exit (by cbv)

private theorem odd :
    graph.ReturnsAfter model (input (args 1)) 1 (graph.initial model (input (args 1))) (-2 : Word) :=
  .backedge (next := bank 1 3 1) (by cbv) (.exit (by cbv))

private theorem even :
    graph.ReturnsAfter model (input (args 2)) 2 (graph.initial model (input (args 2))) (2 : Word) :=
  .backedge (next := bank 1 3 1) (by cbv)
    (.backedge (next := bank 3 1 2) (by cbv) (.exit (by cbv)))

example : lower.oracle 0 [0, 3, 1] mem [2] mem :=
  (lower_returns_iff accepted (args 0) mem mem [2]).mpr ⟨2, ⟨0, zero⟩, rfl, rfl⟩

example :
    ∃ start finish, lower.start 0 [1, 3, 1] mem = some start ∧
      StepsNWithin lower [] 11 start finish ∧ step lower finish = .returned [-2] mem :=
  (lower_stepsN_iff accepted (args 1) mem mem [-2] 11).mpr ⟨1, -2, odd, rfl, rfl, rfl⟩

example :
    ∃ start finish, lower.start 0 [2, 3, 1] mem = some start ∧
      StepsNWithin lower [] 15 start finish ∧ step lower finish = .returned [2] mem :=
  (lower_stepsN_iff accepted (args 2) mem mem [2] 15).mpr ⟨2, 2, even, rfl, rfl, rfl⟩

example : lower.runMain 8 0 [0, 3, 1] mem = .returned [2] mem := by cbv
example : lower.runMain 12 0 [1, 3, 1] mem = .returned [-2] mem := by cbv
example : lower.runMain 16 0 [2, 3, 1] mem = .returned [2] mem := by cbv
example : (lower.runMain 11 0 [1, 3, 1] mem).returnedValues? = none := by cbv

-- Both sources are also destinations. Either in-place copy order would
-- duplicate one payload word instead of producing the bank (1, 3, 1).
example : incomingRegisters .backedge = [.second, .first, .node 1] := rfl

private def firstFeedback : Option (Word × Word × Word) :=
  match lower.runMain 7 0 [1, 3, 1] mem with
  | .running s => do
    if s.point.label = 1 ∧ s.point.index = 0 then
      return (← s.frame.get .first, ← s.frame.get .second, ← s.frame.get .index)
    else none
  | _ => none

example : firstFeedback = some (1, 3, 1) := by cbv

private def duplicatedFeedback : NativeGraph :=
  { graph with
    phiInputs
      | .entry => graph.phiInputs .entry
      | .backedge =>
        let wires := graph.phiInputs .backedge
        let first := wires.get (.tail .head)
        .cons first (.cons first (.cons (wires.get (.tail (.tail .head))) .nil)) }

example : lowerChecked duplicatedFeedback = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank
