module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Thms
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step

open SCCP.Example.Bank (model facts)
open Phi.Support.Example (before)
open Step.Example (index noOp transitiveWake feedbackActivation)

#guard noOp = (true, (.constant true, .constant 255), [.result], [.phi (1 : Fin 2)])
#guard transitiveWake =
  (true, (.constant true, .constant 255), [.control, .phi (0 : Fin 2), .phi (1 : Fin 2)], [.phi (1 : Fin 2)])
#guard feedbackActivation =
  (true, (.constant true, .constant 255), [.phi (1 : Fin 2), .phi (0 : Fin 2)], [.control])

example :
    Index.runSteps model (facts true 255) index 1 before [.phi (1 : Fin 2), .result] =
      FIFO.runSteps (Index.step model (facts true 255) index) 1 before [.phi (1 : Fin 2), .result] :=
  congrFun (congrFun (congrFun (Index.runSteps_eq_step index) _) _) _

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step
