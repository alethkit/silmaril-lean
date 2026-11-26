module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit

open Diamond.SCCP (TupleCovers)
open Example (Carried facts graph input refusesVarying route run)
open PruneExit.Example.Bank (i16)
open SeaOfNodes.MLIR (sourceInputs)
open Loop.MLIR.CF (TargetOp evalOp)
open Loop.MLIR.CF.Bank (Label lower)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.MLIR.Pure (Code)

private def onlyHeader {Δ : List Width} : Code TargetOp (Terminator (Label Carried i16) [i16]) Δ → Bool
  | .terminator (.br edge) => PruneExit.Bank.isHeader edge.label
  | .terminator _ => false
  | .letOp _ _ rest => onlyHeader rest

private theorem accepted : rewrite graph (facts (.constant 0)) = some (directFeedback graph) := rfl

example : onlyHeader ((lower graph).block .header) = false := rfl
example : (rewrite graph (facts (.constant 0))).map (fun cfg => onlyHeader (cfg.block .header)) = some true := rfl

-- Updating the final field after overwriting the first would give five on the first step.
example : route 1 300 4 = some (4, 302, 2) := rfl
example : route 4 302 2 = some (2, 304, 5) := rfl

example : (lower graph).run evalOp 3 (input 1) = some (.cons 300 .nil) := rfl
example : run (.constant 1) 3 1 = none := rfl
example : run .overdefined 8 0 = none := rfl
example : run .bottom 8 0 = none := rfl
example : refusesVarying = true := rfl

private theorem covered : TupleCovers (facts (.constant 0)) (sourceInputs (input 0)) := by
  intro sort port
  cases port with
  | head => rfl
  | tail p => cases p

example (budget : Nat) :
    (directFeedback graph).run evalOp budget (input 0) = none ∧
      (lower graph).run evalOp budget (input 0) = none :=
  runs_none accepted covered budget

example :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (directFeedback graph)).denotePart evalOp (input 0) = Part.none :=
  denotePart_eq_none accepted covered

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit
