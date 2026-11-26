module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA

open Memory.Diamond.LambdaSSA (Instruction inputEnv packet wordPacket)
open Fixture
open Isotope.LambdaSSA.Semantics.Region (Eval)

example : (lower shift).HasType (inputContext args) [wordPacket] := lower_hasType shift

example : (edge shift .entry).target = (edge shift .backedge).target := rfl
example : edge shift .entry ≠ edge shift .backedge := incoming_distinct shift
example : (phiView shift).table.branch (edge shift .backedge) = .br 0 .unit := edge_branch shift .backedge

private theorem immediateSource : shift.ReturnsAfter input (initial 0) 0 0 (update (initial 0) 2) :=
  (shift.returnsAfter_iff_evalAfter input (initial 0) 0 0 (update (initial 0) 2)).mpr (by cbv)

private theorem repeatSource : shift.ReturnsAfter input (initial 1) 2 0 atExit :=
  (shift.returnsAfter_iff_evalAfter input (initial 1) 2 0 atExit).mpr (by cbv)

-- Exit at once, after copying the tail and clearing it in the actual CFG.
example : FollowAfter shift input 0 (initial 0) 0 (update (initial 0) 2) :=
  (returnsAfter_iff shift input (initial 0) 0 0 (update (initial 0) 2)).mp immediateSource

example : Eval (Instruction 3) (inputEnv input) (lower shift) (initial 0) 0
    (packet 0) (update (initial 0) 2) :=
  (returns_iff shift input (initial 0) 0 (update (initial 0) 2)).mp ⟨0, immediateSource⟩

-- A later activation sees the forwarded heap, reads 2, and writes the next heap.
private theorem laterActivation : Activation shift input afterEntry 0 .unit afterBackedge :=
  (activation_backedge_iff shift input afterEntry afterBackedge).mpr
    ⟨2, (bodyTable.returns_iff_denote input afterEntry 2 afterBackedge).mpr (by cbv), by cbv⟩

private theorem exitActivation : Activation shift input afterBackedge 1 (packet 0) atExit :=
  (activation_exit_iff shift input afterBackedge 0 atExit).mpr
    ⟨(bodyTable.returns_iff_denote input afterBackedge 0 atExit).mpr (by cbv), by cbv⟩

example : shift.ReturnsFrom input (initial 1) .backedge afterEntry 1 0 atExit :=
  (returnsFrom_iff shift input (initial 1) .backedge afterEntry 1 0 atExit).mpr
    (.backedge laterActivation (.exit exitActivation))

example : FollowAfter shift input 2 (initial 1) 0 atExit :=
  (returnsAfter_iff shift input (initial 1) 2 0 atExit).mp repeatSource

example : Eval (Instruction 3) (inputEnv input) (lower shift) (initial 1) 0 (packet 0) atExit :=
  (returns_iff shift input (initial 1) 0 atExit).mp ⟨2, repeatSource⟩

example : ¬ FollowAfter shift input 1 (initial 1) 0 atExit := by
  intro run
  have returned := (returnsAfter_iff shift input (initial 1) 1 0 atExit).mpr run
  have evaluated := (shift.returnsAfter_iff_evalAfter input (initial 1) 1 0 atExit).mp returned
  have none : shift.evalAfter input (initial 1) 1 = none := by cbv
  rw [none] at evaluated
  cases evaluated

end Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA
