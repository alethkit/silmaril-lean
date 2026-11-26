module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open Fixture
open Memory.Diamond.LambdaSSA (Instruction inputEnv packet)
open RVSDG.NestedTheta.Petri (Finishes)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private theorem observe (heap : Heap 3) (backedges : Nat) (final : Heap 3)
    (returned : shift.evalAfter input heap backedges = some (0, final)) :
    Portable.Observation shift input heap backedges 0 final :=
  (shift.returnsAfter_iff_portable input heap backedges 0 final).mp
    ((shift.returnsAfter_iff_evalAfter input heap backedges 0 final).mpr returned)

-- The first activation exits after its stores, even at backedge count zero.
private theorem immediate : Portable.Observation shift input (initial 0) 0 0 (update (initial 0) 2) :=
  observe (initial 0) 0 (update (initial 0) 2) (by cbv)

example : (shift.lowerTheta.run (thetaRuntime 3) 0 (encodeInput (initial 0) input) = none) ∧
    (shift.lowerTheta.run (thetaRuntime 3) 1 (encodeInput (initial 0) input) =
      some (encodeResult 0 (update (initial 0) 2))) :=
  ⟨immediate.thetaBefore, immediate.thetaAt⟩

example : Eval (Instruction 3) (inputEnv input) (LambdaSSA.lower shift) (initial 0) 0
      (packet 0) (update (initial 0) 2) ∧
    Finishes (thetaRuntime 3) shift.lowerTheta (encodeInput (initial 0) input)
      (encodeResult 0 (update (initial 0) 2)) :=
  ⟨immediate.lambdaReturn, immediate.petriCompletion⟩

-- The second backedge leads to the third numbered activation and its exit.
private theorem repeated : Portable.Observation shift input (initial 1) 2 0 atExit :=
  observe (initial 1) 2 atExit (by cbv)

example : (shift.lowerTheta.run (thetaRuntime 3) 2 (encodeInput (initial 1) input) = none) ∧
    (shift.lowerTheta.run (thetaRuntime 3) 3 (encodeInput (initial 1) input) =
      some (encodeResult 0 atExit)) :=
  ⟨repeated.thetaBefore, repeated.thetaAt⟩

example : Eval (Instruction 3) (inputEnv input) (LambdaSSA.lower shift) (initial 1) 0 (packet 0) atExit ∧
    Finishes (thetaRuntime 3) shift.lowerTheta (encodeInput (initial 1) input) (encodeResult 0 atExit) :=
  ⟨repeated.lambdaReturn, repeated.petriCompletion⟩

example :
    ∃ backedges, Portable.Observation shift input (initial 1) backedges 0 atExit :=
  (shift.returns_iff_portable input (initial 1) 0 atExit).mp
    ((shift.lowerTheta_finishes_iff input (initial 1) 0 atExit).mpr repeated.petriCompletion)

end Silmaril.SSA.SeaOfNodes.Memory.Loop
