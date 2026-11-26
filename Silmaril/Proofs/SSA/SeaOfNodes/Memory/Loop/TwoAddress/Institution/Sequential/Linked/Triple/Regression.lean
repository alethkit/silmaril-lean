module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple

open Memory.Diamond.Institution renaming Model → EntryModel
open Sequential.Fixture (captures graph initial right)
open Linked.Fixture (combined first wiring inputs)

-- The third loop uses the second loop's store capture as its stop word
-- and uses the second return as its own store payload.
private def thirdWiring : Boundary.Wiring captures.args captures.args :=
  .forward .head (.forward (.tail .head) (.forward (.tail (.tail (.tail .head)))
    (.word fun p => nomatch p)))

private def entryModel : EntryModel combined := ⟨6, inputs⟩

private def afterFirst : Heap 6 := (initial.write 0 11).write 2 11
private def afterSecond : Heap 6 := (afterFirst.write 3 22).write 5 22
private def expected : Result 6 := (3, 3, 22, afterSecond.write (right 0) 3)

private def run (fuel : Nat) : Option (Word × Word × Word × List Word) :=
  ((program first graph graph wiring thirdWiring).graph.run (thetaRuntime 6) fuel (encodeInput initial inputs)).map
    fun raw =>
      let (firstWord, secondWord, thirdWord, heap) := (resultCodec 6).symm raw
      (firstWord, secondWord, thirdWord, (List.finRange 6).map heap)

#guard (run 1).isNone
#guard run 2 == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

private def thirdInput := thirdWiring.select (3 : Word) (wiring.select (3 : Word) inputs)

-- The same typed captures and budget cannot return from the stale heap.
#guard ((Petri.lower graph).run (thetaRuntime 6) 2 (encodeInput initial thirdInput)).isNone

private theorem staged :
    ∃ firstHeap secondHeap,
      (Petri.lower first).Returns (thetaRuntime 6) (encodeInput initial inputs) (encodeResult 3 firstHeap) ∧
      (Petri.lower graph).Returns (thetaRuntime 6) (encodeInput firstHeap (wiring.select 3 inputs))
        (encodeResult 3 secondHeap) ∧
      (Petri.lower graph).Returns (thetaRuntime 6) (encodeInput secondHeap thirdInput)
        (encodeResult 22 expected.2.2.2) := by
  exact ⟨afterFirst, afterSecond, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩

example : RVSDG.NestedTheta.Petri.Finishes (thetaRuntime 6) (lower first graph graph wiring thirdWiring)
    (encodeInput initial inputs) (resultCodec 6 expected) := by
  apply (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).mpr
  exact (returns_iff_stages (P := combined) (Q := captures) (R := captures) first graph graph
    wiring thirdWiring entryModel initial _ 3 3 22).mpr staged

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple
