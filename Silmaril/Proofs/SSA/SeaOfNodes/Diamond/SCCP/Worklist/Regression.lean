module

import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example.Defs

open Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist

example : report (.constant ⟨true⟩) = ([.branch, .producers, .branch, .phi], false, true, .constant 14) := by
  decide

example : report .overdefined = ([.branch, .producers, .branch, .phi], true, true, .overdefined) := by
  decide

-- No guard fact ever arrives, so neither branch nor Phi needs to be queued again.
example : report .bottom = ([.branch, .producers], false, false, .bottom) := by decide

-- Learning the unmarked false operand queues nothing. Learning the marked true operand queues just Phi.
example : pendingAfterLearning 3 = [] := by decide
example : pendingAfterLearning 2 = [.phi] := by decide

-- The predicate is watched independently of the Phi operand facts.
example : pendingAfterLearning 0 = [.branch] := by decide

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist
