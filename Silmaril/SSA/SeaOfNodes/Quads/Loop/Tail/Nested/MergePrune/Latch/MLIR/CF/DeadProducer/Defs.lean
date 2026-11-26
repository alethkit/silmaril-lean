module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer.Defs

/-! # Emit the checked shorter pure CF latch -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open Diamond.Prune (HeaderProjection)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)
variable (cut : Split.DeadProducer.Checked checked.latchTransfer)

/-- Reuse the certified CFG and emit the shortened table at the same latch label. -/
def lower : Target (carry := carry) (merge := merge) (atLatch := atLatch) p :=
  withLatch p (CF.lower p projected checked) (latchCode p cut.erased.flow cut.outgoing)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer
