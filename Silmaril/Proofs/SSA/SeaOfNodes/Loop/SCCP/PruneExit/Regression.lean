module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Bank.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit

open Example (exitFacts varyingFacts unseenFacts continueFacts run)
open Loop.Portable.Example (graph input width)
open Loop.MLIR.CF (TargetOp evalOp)
open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.MLIR.Pure (Code)

private def successorCount {Δ carried : List Width} {result : Width} :
    Code TargetOp (Terminator (Loop.MLIR.CF.Bank.Label carried result) [result]) Δ → Nat
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

section CarriedBank

open Example.Bank (i16)
open Diamond.SCCP (TupleCovers)

local notation "bankGraph" => Example.Bank.graph
local notation "bankInput" => Example.Bank.input

example : successorCount ((Loop.MLIR.CF.Bank.lower bankGraph).block .header) = 2 := rfl

example :
    (Bank.rewrite bankGraph Example.Bank.exitFacts).map (fun cfg => successorCount (cfg.block .header)) = some 1 :=
  rfl

-- Distinct widths and payloads check both the order and the selected argument.
example : (Loop.MLIR.CF.Bank.lower bankGraph).entry.eval evalOp (fun term env => term.eval env)
    (bankInput 5 300 4) = .inl ⟨.header, .cons 5 (.cons 300 .nil)⟩ := rfl

example : ((Loop.MLIR.CF.Bank.lower bankGraph).block .header).eval evalOp (fun term env => term.eval env)
    (.cons 2 (.cons 300 (bankInput 2 300 4))) = .inl ⟨.header, .cons 3 (.cons 302 .nil)⟩ := rfl

example : ((Bank.directExit bankGraph).block .header).eval evalOp (fun term env => term.eval env)
    (.cons 5 (.cons 300 (bankInput 5 300 4))) = .inl ⟨.exit, .cons 300 .nil⟩ := rfl

example : Example.Bank.run Example.Bank.exitFacts 3 5 300 = some (some 300) := rfl
example : Example.Bank.run Example.Bank.exitFacts 2 5 300 = some none := rfl
example : (Loop.MLIR.CF.Bank.lower bankGraph).run evalOp 5 (bankInput 2 300 4) = some (.cons 304 .nil) := rfl
example : Example.Bank.run Example.Bank.varyingFacts 5 2 300 = none := rfl
example : Example.Bank.run Example.Bank.unknownFacts 3 5 300 = none := rfl
example : Example.Bank.run Example.Bank.unseenFacts 3 5 300 = none := rfl

private theorem payloadCovered (payload : Word i16) :
    TupleCovers Example.Bank.exitFacts (sourceInputs (bankInput 5 payload 4)) := by
  intro sort port
  cases port with
  | head => rfl
  | tail port =>
    cases port with
    | head => trivial
    | tail port =>
      cases port with
      | head => rfl
      | tail port => cases port

example (payload : Word i16) (fuel : Nat) :
    (Bank.directExit bankGraph).run evalOp fuel (bankInput 5 payload 4) =
      (Loop.MLIR.CF.Bank.lower bankGraph).run evalOp fuel (bankInput 5 payload 4) :=
  Bank.run_eq (facts := Example.Bank.exitFacts) rfl (payloadCovered payload) fuel

end CarriedBank

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit
