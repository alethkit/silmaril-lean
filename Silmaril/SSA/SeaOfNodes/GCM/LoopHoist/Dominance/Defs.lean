module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs

/-! # Dominator addresses for the three-block pure loop lowering -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance

open Silmaril.MLIR.Arith (Width)

variable {carried result : Width}

/-- The structural chain from the preheader through the header to the exit. -/
def stage : BlockId (SourceLabel carried result) → Nat
  | none => 0
  | some ⟨_, .header⟩ => 1
  | some ⟨_, .exit⟩ => 2

def address (block : BlockId (SourceLabel carried result)) : List Nat :=
  List.replicate (stage block) 0

/-- Exact slots of the existing lowering. The header's true slot is its
self-backedge and its false slot transfers the exit operand. -/
def expectedTarget : BlockId (SourceLabel carried result) → EdgeSlot →
    Option (Target (SourceLabel carried result))
  | none, .jump => headerId
  | some ⟨_, .header⟩, .onTrue => headerId
  | some ⟨_, .header⟩, .onFalse => some ⟨_, .exit⟩
  | _, _ => none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance
