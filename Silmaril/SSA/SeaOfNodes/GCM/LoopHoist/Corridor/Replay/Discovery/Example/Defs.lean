module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example.Defs

/-! # Discover a dependent chain and stop at a latch-dependent binding -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example

open Silmaril.MLIR.Arith (Width)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (word Inputs input)
open AfterReorder.Second.Example (first)

def chain : Except Refusal (Plan Inputs word word) :=
  discover Step.Example.loop first.header

def varying : Except Refusal (Plan Inputs word word) :=
  discover (AfterReorder.Second.Example.loop true) first.header

def unsaved : Except Refusal (Plan Inputs word word) :=
  discover (Corridor.Example.loop true) []

/-- Observe the chosen origin/cut pairs, surviving header order, next candidate,
and outcomes at fuel three through five. -/
def observe (search : Except Refusal (Plan Inputs word word)) :
    Except Refusal (List (Nat × Nat) × List Nat × Option Nomination × List (Option Nat)) :=
  search.map fun plan =>
    (plan.requests.map (fun request => (request.origin, request.cut)), plan.output.origins, next? plan.output,
      [3, 4, 5].map fun fuel => (plan.output.cfg.run evalOp fuel (input 2 10 1)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
