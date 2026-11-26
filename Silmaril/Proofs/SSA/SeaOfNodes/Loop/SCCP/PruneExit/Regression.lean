module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit

open Example (exitFacts varyingFacts unseenFacts continueFacts run)
open Loop.Portable.Example (graph input width)
open Loop.MLIR.CF (Label TargetOp evalOp)
open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.MLIR.Pure (Code)

private def successorCount {Δ : List Width} :
    Code TargetOp (Terminator (Label width width) [width]) Δ → Nat
  | .terminator (.br _) => 1
  | .terminator (.condBr ..) => 2
  | .terminator (.ret _) => 0
  | .letOp _ _ rest => successorCount rest

private theorem originalHasBackedge :
    successorCount ((Loop.MLIR.CF.lower graph).block .header) = 2 := rfl

private theorem removesSuccessor :
    (rewrite graph exitFacts).map (fun cfg => successorCount (cfg.block .header)) = some 1 := rfl

-- With this input the old backedge would carry 7. The retained exit carries 10.
private theorem routedExitPayload :
    ((directExit graph).block .header).eval evalOp (fun term env => term.eval env)
      (.cons 5 (input 5 4 2)) = .inl ⟨.exit, .cons 10 .nil⟩ := rfl

private theorem exactBudget : run exitFacts 3 5 4 2 = some (some 10) := rfl
private theorem shortBudget : run exitFacts 2 5 4 2 = some none := rfl

private theorem varyingFirstStep :
    graph.step Loop.MLIR.CF.model (sourceInputs (input 0 4 1)) (.cons (0 : Word width) .nil) =
      .inr (.cons (1 : Word width) .nil) := rfl

private theorem varyingExitStep :
    graph.step Loop.MLIR.CF.model (sourceInputs (input 0 4 1)) (.cons (4 : Word width) .nil) = .inl (4 : Word width) := rfl

private theorem varyingRunReachesExit :
    (Loop.MLIR.CF.lower graph).run evalOp 7 (input 0 4 1) = some (.cons (4 : Word width) .nil) := rfl

private theorem refusesVarying : run varyingFacts 7 0 4 1 = none := rfl
private theorem refusesUnseen : run unseenFacts 3 5 4 1 = none := rfl
private theorem refusesContinue : run continueFacts 4 0 4 0 = none := rfl

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit
