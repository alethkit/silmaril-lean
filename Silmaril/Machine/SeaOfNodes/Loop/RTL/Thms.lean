module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Correctness

/-! # Finite returns and exact header transfers -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (CallOracle Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)

/-- The emitted function satisfies the machine SSA signature, definition,
dominance and block argument checks. -/
theorem lower_wellFormed : lowerFunc.WellFormed := by decide

/-- Machine execution returns exactly the source's singleton word and
preserves the entire memory, for all machine-word seeds and strides. -/
theorem lower_returns_iff (seed delta : Word) (initial final : Memory) (returned : List Word) :
    lower.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, graph.Returns model (entry seed delta) value ∧
        returned = [value] ∧ final = initial :=
  Proofs.lower_returns_iff seed delta initial final returned

/-- The actual terminator operand of each source occurrence enters the same
header parameter. The two occurrences are indexed by source label and ordinal. -/
theorem incoming_operand (edge : Incoming) :
    ((lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, [incomingRegister edge]) :=
  Proofs.incoming_operand edge

theorem latch_entry (seed delta : Word) :
    graph.initial model (entry seed delta) = .cons seed .nil :=
  Proofs.latch_entry seed delta

theorem latch_feedback (seed delta old : Word) :
    let args := appendTuple (Tuple.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
    graph.latch model .backedge args (graph.header.eval model args PUnit.unit) =
      .cons (old - delta) .nil :=
  Proofs.latch_feedback seed delta old

/-- Transfer reads the actual incoming register before rebinding Phi. All
other registers, the stack and memory retain their pre-transfer state. -/
theorem transfer_incoming (edge : Incoming) (s : State Reg) (value : Word)
    (func : s.point.func = 0) (read : s.frame.get (incomingRegister edge) = some value) :
    transfer lower s 1 [incomingRegister edge] =
      .running ⟨⟨0, 1, 0⟩, s.frame.set .phi value, s.stack, s.mem⟩ :=
  Proofs.transfer_incoming edge s value func read

/-- Executing the actual producer instructions updates exactly the three
results in the post-operation frame and leaves memory unchanged. -/
theorem header_exec_iff (oracle : CallOracle) (fr done : Frame Reg) (mem final : Memory)
    (old delta : Word) (hold : fr.get .phi = some old)
    (hdelta : fr.get (.arg 1) = some delta) :
    Ops.Exec oracle header.ops fr mem done final ↔
      done = headerFrame fr old delta ∧ final = mem :=
  Proofs.header_exec_iff oracle fr done mem final old delta hold hdelta

/-- Executing the preheader's terminator binds the source entry latch. -/
theorem step_entry (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (seed : Word) (read : fr.get (.arg 0) = some seed) :
    step lower ⟨⟨0, 0, 0⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, fr.set .phi seed, stack, mem⟩ :=
  Proofs.step_entry fr stack mem seed read

/-- A taken feedback branch binds the source backedge latch from the
producer frame, leaving the remainder of that frame untouched. -/
theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (old delta : Word) (taken : old - delta ≠ 0) :
    let after := headerFrame fr old delta
    step lower ⟨⟨0, 1, header.ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, after.set .phi (old - delta), stack, mem⟩ :=
  Proofs.step_feedback fr stack mem old delta taken

end Silmaril.Machine.SeaOfNodes.Loop.RTL
