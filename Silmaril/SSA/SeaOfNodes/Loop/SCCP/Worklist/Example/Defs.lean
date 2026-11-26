module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Thms

/-! Observe the same scalar and typed-bank loops under FIFO scheduling. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example

open Semantics.Dataflow (Flat)
open SCCP.Example (Byte model graph facts word)
open Diamond.SCCP (tupleFacts)

/-- Visited jobs, backedge and exit marks, then the latch and return facts. -/
def report (amount : Byte) (enabled : Flat (ULift Bool)) : List Task × Bool × Bool × Flat Nat × Flat Nat :=
  let result := run model (graph amount) (facts 0 enabled)
  (result.visits, decide (incomingIndex .backedge ∈ result.state.1),
    decide (exitIndex ∈ result.state.1),
    (result.state.2.1 (0 : Fin 1)).map BitVec.toNat, result.state.2.2.map BitVec.toNat)

/-- Latch after a prefix of the queue trace for increment-one feedback. -/
def latchAfter (jobs : Nat) : Flat Nat :=
  let result := runSteps model (graph 1) (facts 0 (.constant ⟨true⟩)) jobs ⊥ initial
  (result.state.2.1 (0 : Fin 1)).map BitVec.toNat

def bankReport : (Flat Bool × Flat Nat) × Flat Nat :=
  let result := run SCCP.Example.Bank.model (SCCP.Example.Bank.graph false) (SCCP.Example.Bank.facts true 0)
  (SCCP.Example.Bank.observe result.state.2.1, result.state.2.2.map BitVec.toNat)

/-- One Phi visit on a backedge-only assignment with a chosen queue tail. -/
def crossFeedback (pending : List Task) : (Flat Bool × Flat Nat) × List Task :=
  let entry := SCCP.Example.Bank.facts false 0
  let old : State SCCP.Example.Bank.model.value SCCP.Example.Bank.fields word :=
    ({incomingIndex .backedge}, tupleFacts entry, ⊥)
  let next := step SCCP.Example.Bank.model (SCCP.Example.Bank.graph true) entry .phi old pending
  (SCCP.Example.Bank.observe next.1.2.1, next.2)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Example
