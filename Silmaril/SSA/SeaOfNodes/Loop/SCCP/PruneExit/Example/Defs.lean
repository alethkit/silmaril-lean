module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Portable.Example.Defs

/-! Try pruning the portable counter with known, varying, or unseen guards. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example

open Loop.Portable.Example (graph input width)
open Loop.MLIR.CF (evalOp)
open SeaOfNodes.MLIR (Word)

def exitFacts : InputFacts [width, width, width] :=
  .cons (.constant (5 : Word width)) (.cons (.constant (4 : Word width)) (.cons .overdefined .nil))

def varyingFacts : InputFacts [width, width, width] :=
  .cons (.constant (0 : Word width)) (.cons (.constant (4 : Word width)) (.cons (.constant (1 : Word width)) .nil))

def unseenFacts : InputFacts [width, width, width] :=
  .cons .bottom (.cons (.constant (4 : Word width)) (.cons (.constant (1 : Word width)) .nil))

def continueFacts : InputFacts [width, width, width] :=
  .cons (.constant (0 : Word width)) (.cons (.constant (4 : Word width)) (.cons (.constant (0 : Word width)) .nil))

/-- Report refusal as the outer `none` and budget exhaustion as `some none`. -/
def run (facts : InputFacts [width, width, width]) (fuel : Nat)
    (start limit step : Word width) : Option (Option Nat) :=
  (rewrite graph facts).map fun cfg =>
    (cfg.run evalOp fuel (input start limit step)).map fun values => (values.get .here).toNat

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example
