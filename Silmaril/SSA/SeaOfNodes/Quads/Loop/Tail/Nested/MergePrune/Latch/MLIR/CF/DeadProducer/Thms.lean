module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer.Thms

/-! # Actual shortened latch packets and independent finite-return budgets -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)
variable (cut : Split.DeadProducer.Checked checked.latchTransfer)
variable (input : Bank (regs := regs) model)

/-- All packet fields are read in the shorter table before branching. -/
theorem latch_packet (old : Bank (regs := atLatch.kept) model) :
    ((lower p projected checked cut).block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (packetFrame p (checked.latchTransfer.eval model old)) :=
  (CF.latchCode_eval p cut.erased.flow cut.outgoing input old).trans
    (congrArg (fun packet => Sum.inl (packetFrame (merge := merge) (atLatch := atLatch) p packet))
      (cut.eval_agrees model old))

/-- The revised code at the same tested label has identical evaluated edges. -/
theorem latch_frame (old : Bank (regs := atLatch.kept) model) :
    ((lower p projected checked cut).block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      ((CF.lower p projected checked).block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) :=
  (latch_packet p projected checked cut input old).trans
    (CF.latchCode_eval p checked.latchTransfer.flow checked.latchTransfer.outgoing input old).symm

theorem lower_run (fuel : Nat) :
    (lower p projected checked cut).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) :=
  CF.withLatch_lower_run p projected checked _ input
    (fun old => latch_frame p projected checked cut input (atLatch.project old)) fuel

theorem run_agrees (fuel : Nat) :
    (lower p projected checked cut).run evalOp fuel (encodeValues input) =
      (CF.lower p projected checked).run evalOp fuel (encodeValues input) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [lower_run, CF.lower_run]

theorem source_returns_iff (output : Env [valueWidth out]) :
    (∃ fuel, (lower p projected checked cut).run evalOp fuel (encodeValues input) = some output) ↔
      ∃ fuel, (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) = some output := by
  simpa only [run_agrees] using CF.source_returns_iff p projected checked input output

theorem source_diverges_iff :
    (lower p projected checked cut).Diverges evalOp (encodeValues input) ↔
      ∀ fuel, src.runFrom model fuel entry input = none := by
  simpa only [Silmaril.MLIR.CF.Cfg.Diverges, run_agrees] using CF.source_diverges_iff p projected checked input

variable (result : KeptResult p (mask := carry))

/-- The numbered endpoint still counts θ activations. CF counts original
block visits and the final typed return. -/
theorem cf_at_activations (activations : Nat) :
    (lower p projected checked cut).run evalOp (sourceVisits p model activations input + 1) (encodeValues input) =
      ((Latch.Numbered.lower p projected checked.whole result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) := by
  simpa only [run_agrees] using CF.Comparison.cf_at_activations p projected checked result input activations

theorem numbered_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (lower p projected checked cut).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((Latch.Numbered.lower p projected checked.whole result).run (Join.model model)
        activations input).map (encodeValues (ins := [out])) = some output := by
  simpa only [run_agrees] using CF.Comparison.cf_returns_iff p projected checked result input output

theorem numbered_diverges_iff :
    (lower p projected checked cut).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (Latch.Numbered.lower p projected checked.whole result).run (Join.model model)
        activations input = none := by
  simpa only [Silmaril.MLIR.CF.Cfg.Diverges, run_agrees] using
    CF.Comparison.cf_diverges_iff p projected checked result input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer
