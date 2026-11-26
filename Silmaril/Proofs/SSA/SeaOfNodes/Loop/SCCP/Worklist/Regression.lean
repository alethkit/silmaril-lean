module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist

-- A successful backedge invalidates Phi, and changing the latch invalidates it again.
example : latchAfter 3 = .constant 0 := by decide
example : latchAfter 5 = .overdefined := by decide
example : report 1 (.constant ⟨true⟩) =
    ([.control, .control, .phi, .control, .phi, .control, .phi, .result],
      true, true, .overdefined, .overdefined) := by decide

-- Equal feedback keeps the latch and stops re-enqueuing Phi.
example : report 0 .overdefined =
    ([.control, .control, .phi, .control, .phi, .result], true, true, .constant 0, .constant 0) := by decide

-- Exit-only control does not create another Phi visit.
example : report 1 (.constant ⟨false⟩) =
    ([.control, .control, .phi, .control, .result], false, true, .constant 0, .constant 1) := by decide

example : bankReport = ((.constant true, .overdefined), .overdefined) := by decide

-- Native feedback from (false, 0) is (true, 0). The word reads the old flag.
example : crossFeedback [] = ((.constant true, .constant 0), [.phi]) := by decide
example : crossFeedback [.result, .phi] = ((.constant true, .constant 0), [.result, .phi]) := by decide

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist
