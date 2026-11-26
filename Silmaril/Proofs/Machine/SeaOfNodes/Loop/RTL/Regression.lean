module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (entry model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)

private def mem : Memory := Memory.ofList 4 [19, 37, 81, 5]

private theorem zeroBackedges :
    graph.ReturnsAfter model (entry 2 2) 0 (graph.initial model (entry 2 2)) (2 : Word) :=
  .exit (by cbv)

private def carried (old : Word) : Tuple (Val model.value) [.value word] := .cons old .nil

private theorem twoBackedges :
    graph.ReturnsAfter model (entry 3 1) 2 (graph.initial model (entry 3 1)) (1 : Word) :=
  .backedge (next := carried 2) (by cbv)
    (.backedge (next := carried 1) (by cbv) (.exit (by cbv)))

example : lower.oracle 0 [2, 2] mem [2] mem :=
  (lower_returns_iff 2 2 mem mem [2]).mpr ⟨2, ⟨0, zeroBackedges⟩, rfl, rfl⟩

example : lower.oracle 0 [3, 1] mem [1] mem :=
  (lower_returns_iff 3 1 mem mem [1]).mpr ⟨1, ⟨2, twoBackedges⟩, rfl, rfl⟩

example : lower.runMain 6 0 [2, 2] mem = .returned [2] mem := by cbv
example : lower.runMain 14 0 [3, 1] mem = .returned [1] mem := by cbv

-- Observe machine states at header entry, just after each transfer.
private def headerLatch (fuel : Nat) : Option Word :=
  match lower.runMain fuel 0 [3, 1] mem with
  | .running s =>
    if s.point.label = 1 ∧ s.point.index = 0 then s.frame.get .phi else none
  | _ => none

example : headerLatch 1 = some 3 := by cbv
example : headerLatch 5 = some 2 := by cbv
example : headerLatch 9 = some 1 := by cbv

example : incomingSlot .entry = (0, 0) ∧ incomingRegister .entry = .arg 0 := ⟨rfl, rfl⟩
example : incomingSlot .backedge = (1, 0) ∧ incomingRegister .backedge = .node 0 := ⟨rfl, rfl⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL
