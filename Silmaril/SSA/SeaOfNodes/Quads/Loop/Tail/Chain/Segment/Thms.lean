module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Correctness

/-! # Exact visit accounting for checked jump segments -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (ValueSort Signature Model)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site : Fin size}
variable (path : Segment src target site) (m : Model.{u, v, w} Op)

theorem Segment.run_segment (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + path.blocks.length) site old =
      src.runFrom m fuel target (path.quads.eval m old) :=
  Segment.Proofs.run_segment path m fuel old

theorem Segment.run_short (fuel : Nat) (old : Bank (regs := regs) m)
    (short : fuel < path.blocks.length) : src.runFrom m fuel site old = none :=
  Segment.Proofs.run_short path m fuel old short

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
