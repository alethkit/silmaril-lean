module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open Fixture
open RVSDG.NestedTheta.Petri (Finishes)

-- A zero-backedge completion still publishes both Stores' heap.
example : Finishes (thetaRuntime 3) shift.lowerTheta (encodeInput (initial 0) input)
    (encodeResult 0 (update (initial 0) 2)) := by
  apply (shift.lowerTheta_finishes_iff input (initial 0) 0 (update (initial 0) 2)).mp
  exact ⟨0, (shift.returnsAfter_iff_evalAfter input (initial 0) 0 0 (update (initial 0) 2)).mpr (by cbv)⟩

-- The first activation publishes the continuing tag and its updated heap.
example : Finishes (thetaRuntime 3) shift.activation (encodeInput (initial 1) input)
    (.cons (continueTag 1 0) (encodeInput afterEntry input)) :=
  (shift.activation_finishes_iff input (initial 1) _).mpr (by cbv)

-- The next activation observes the preceding write to the same address.
example : Finishes (thetaRuntime 3) shift.activation (encodeInput afterEntry input)
    (.cons (continueTag 2 0) (encodeInput afterBackedge input)) :=
  (shift.activation_finishes_iff input afterEntry _).mpr (by cbv)

example : Finishes (thetaRuntime 3) shift.lowerTheta (encodeInput (initial 1) input)
    (encodeResult 0 atExit) := by
  apply (shift.lowerTheta_finishes_iff input (initial 1) 0 atExit).mp
  exact ⟨2, (shift.returnsAfter_iff_evalAfter input (initial 1) 2 0 atExit).mpr (by cbv)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop
