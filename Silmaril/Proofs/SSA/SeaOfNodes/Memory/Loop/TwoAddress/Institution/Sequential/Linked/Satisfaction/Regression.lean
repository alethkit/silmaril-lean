module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

open CategoryTheory
open RVSDG (Port)
open RVSDG.NestedTheta.Institution
open Linked.Fixture (combined first wiring inputs)
open Sequential.Fixture (captures graph initial)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Model → EntryModel

private def lhs : Program combined := ⟨captures, first, graph, wiring⟩

-- Identify the right store value with the first stage's store capture.
-- The dependent right stop word continues to come from the first return.
private def identifyStore : combined ⟶ combined :=
  ⟨fun
    | .tail (.tail (.tail (.tail (.tail (.tail .head))))) => .tail (.tail (.tail .head))
    | port => port⟩

private def rhs : Program combined := lhs.map identifyStore
private abbrev entry : EntryModel combined := ⟨6, inputs⟩

example : rhs.numberedObserve entry initial = lhs.numberedObserve (reduct identifyStore entry) initial :=
  lhs.numbered_observe_map identifyStore entry initial

private def middle : Heap 6 := (initial.write 0 11).write 2 11
private def heapAfter (rightWord : Word) : Heap 6 :=
  (middle.write 3 rightWord).write 5 rightWord

private theorem lhsReturned : lhs.nativeReturns entry initial (3, 3, heapAfter 22) :=
  ⟨middle, ⟨1, rfl⟩, ⟨1, rfl⟩⟩

private theorem rhsReturned : rhs.nativeReturns entry initial (3, 3, heapAfter 11) :=
  ⟨middle, ⟨1, rfl⟩, ⟨1, rfl⟩⟩

private theorem mismatch :
    ¬ Agrees (lhs.nativeReturns entry) (rhs.nativeReturns entry) := by
  intro agrees
  have equations := (numbered_agrees lhs rhs entry).mpr agrees initial
  have left := (lhs.numbered_eq_some_iff entry initial (3, 3, heapAfter 22)).mpr lhsReturned
  have right := (rhs.numbered_eq_some_iff entry initial (3, 3, heapAfter 11)).mpr rhsReturned
  have equal := Part.some_inj.mp (left.symm.trans (equations.trans right))
  have cell := congrArg (fun raw => ((resultCodec 6).symm raw).2.2 3) equal
  change (22 : Word) = 11 at cell
  exact (by decide : (22 : Word) ≠ 11) cell

-- The actual existing room rejects this linked equation at count six.
example : ¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 6)) (lhs.equation rhs) :=
  fun holds => mismatch ((equation_satisfaction lhs rhs 6).mp holds entry.input)

example : ¬ Agrees (lhs.colouredReturns entry) (rhs.colouredReturns entry) :=
  fun holds => mismatch ((coloured_agrees lhs rhs entry).mp holds)

private def run (p : Program combined) : Option (Word × Word × List Word) :=
  (p.runMemRef entry 8 ⟨initial⟩).map fun (word, nextWord, heap) =>
    (word, nextWord, (List.finRange 6).map heap.cell)

#guard run lhs == some (3, 3, [11, 73, 11, 22, 91, 22])
#guard run rhs == some (3, 3, [11, 73, 11, 11, 91, 11])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction
