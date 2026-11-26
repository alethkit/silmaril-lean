module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Defs

/-! # Checked explicit later cuts for one binding in the single-latch header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block Cfg)
open Loop.MLIR.CF (Program TargetOp lower)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Check that the original cut gives a later header insertion after removal,
then check the actual operand and use sites on the original lowered CFG. -/
def checkDestination (g : Program Input carried result entrySigs headerSigs)
    (index : Nat) (cut : Point (SourceLabel carried result)) : Bool :=
  let _ := sourceTargetDecEq carried result
  let cfg := lower g
  decide (cut.block = headerId ∧ index < afterRemoval index cut.cut) &&
    (findBinding index 0 headerOrigins (cfg.block .header)).any fun ⟨_, binding⟩ =>
      Dominance.Placement.checkCut cfg blocks binding.operands binding.uses cut

/-- Move one binding across `extraSteps + 1` following bindings in the typed sequence.
Each swap checks the next binding's operands in the current scope. -/
def moveLater? : (index extraSteps : Nat) →
    Block TargetOp (SourceLabel carried result) Γ [result] →
      Option (Block TargetOp (SourceLabel carried result) Γ [result])
  | index, 0, block => swapAt? index block
  | index, extraSteps + 1, block => do
    let block ← swapAt? index block
    moveLater? (index + 1) extraSteps block

/-- Test an explicit destination in original CFG coordinates. Install the
new header only when the destination check and every typed swap pass. -/
def moveAt? (g : Program Input carried result entrySigs headerSigs)
    (index : Nat) (cut : Point (SourceLabel carried result)) :
    Option (Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  let cfg := lower g
  if checkDestination g index cut then
    let insertion := afterRemoval index cut.cut
    (moveLater? index (insertion - index - 1) (cfg.block .header)).map (withHeader cfg)
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later
