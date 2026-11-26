module

public import Silmaril.SSA.SeaOfNodes.Loop.Portable.Thms

/-! One portable counter with captured start, limit, and step. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Portable.Example

open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Env Width)

def width : Width := ⟨8, by decide⟩

abbrev bytePort : Diamond.Ty Width := .value (.data width)
abbrev predicatePort : Diamond.Ty Width := .value .predicate

/-- While the latch is unsigned-less-than the limit, add the captured step.
The exit reads back the latch plus the captured start. -/
def graph : Loop.MLIR.CF.Program [width, width, width] width width []
    [[predicatePort], [bytePort], [bytePort]] where
  preheader := .nil
  header :=
    .cons (.ult width)
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg .head) .nil)) .nil))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (1 : Fin 3) .head) .nil
  predicate := .output (0 : Fin 3) .head
  result := .output (2 : Fin 3) .head

def input (start limit step : Word width) : Env [width, width, width] :=
  .cons start (.cons limit (.cons step .nil))

/-- Run numbered θ and MLIR CF with their respective bounds for the chosen
backedge budget. The pair reports their word results as natural numbers. -/
def run (backedges : Nat) (start limit step : Word width) : Option Nat × Option Nat :=
  let args := input start limit step
  let theta := graph.lowerTheta.run (thetaRuntime Loop.MLIR.CF.model) (backedges + 1) (sourceInputs args)
  let cf := (Loop.MLIR.CF.lower graph).run Loop.MLIR.CF.evalOp (backedges + 3) args
  (theta.map (fun values => (values.get .head).toNat),
    cf.map (fun values => (values.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.Loop.Portable.Example
