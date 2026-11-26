module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open Fixture

-- The mandatory first activation exits with its two stores visible.
example : shift.lowerTheta.run (thetaRuntime 3) 1 (encodeInput (initial 0) input) =
    some (encodeResult 0 (update (initial 0) 2)) := rfl

-- The two-backedge run needs three activations and observes the whole heap.
example : shift.lowerTheta.run (thetaRuntime 3) 2 (encodeInput (initial 1) input) = none := rfl

example : shift.lowerTheta.run (thetaRuntime 3) 3 (encodeInput (initial 1) input) =
    some (encodeResult 0 atExit) := by
  have counted := (shift.returnsAfter_iff_evalAfter input (initial 1) 2 0 atExit).mpr (by cbv)
  exact ((shift.lowerTheta_returnsAfter_iff input (initial 1) 2 0 atExit).mp counted).2

-- The second activation consumes the heap on the previous backedge.
example : shift.thetaBody.run (thetaRuntime 3) (encodeInput afterEntry input) =
    .cons (continueTag 2 0) (encodeInput afterBackedge input) := rfl

private def repeatWrite : Graph Fixture.args :=
  let loaded : RVSDG.Origin Fixture.args [[.word]] .word := .output (0 : Fin 1) .head
  ⟨.load (.latest 0) headWire
    (.store (.latest 0) headWire loaded (.ret (.latest 1) loaded)), rfl, .tail (.tail .head)⟩

private theorem repeats : repeatWrite.step input (initial 1) = .inr (initial 1) := by
  have same : (initial 1).write headCell 1 = initial 1 :=
    Function.update_eq_self headCell (initial 1)
  change Sum.inr ((initial 1).write headCell 1) = _
  rw [same]

-- Every activation performs the load and store, then requests another round.
example (fuel : Nat) :
    repeatWrite.lowerTheta.run (thetaRuntime 3) fuel (encodeInput (initial 1) input) = none :=
  repeatWrite.lowerTheta_run_none_of_fixed_backedge input (initial 1) repeats fuel

end Silmaril.SSA.SeaOfNodes.Memory.Loop
