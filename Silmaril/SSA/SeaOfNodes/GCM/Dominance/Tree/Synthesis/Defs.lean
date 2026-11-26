module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Thms

/-! # Synthesizing dominator addresses from exact typed CFG dominance -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable [DecidableEq (Target Label)]

/-- Enumerate the reachable strict dominators using the existing CFG query. -/
def strictDominators (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (b : BlockId Label) : List (BlockId Label) :=
  (reachableBlocks cfg blocks).filter fun a => decide (a ≠ b) && dominates? cfg blocks a b

/-- Select the strict dominator dominated by every strict dominator.
A parent of `some none` denotes the anonymous entry. -/
def immediateParent? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (b : BlockId Label) : Option (BlockId Label) :=
  let strict := strictDominators cfg blocks b
  strict.find? fun parent => strict.all fun a => dominates? cfg blocks a parent

/-- Follow the parent chain to entry within the supplied bound. Inventory
indices distinguish the children of each parent. -/
def traceAddress? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label)) :
    Nat → BlockId Label → Option (List Nat)
  | _, none => some []
  | 0, some _ => none
  | fuel + 1, some child => do
    let parent ← immediateParent? cfg blocks (some child)
    let path ← traceAddress? cfg blocks fuel parent
    return path ++ [(reachableBlocks cfg blocks).idxOf (some child)]

/-- The reachable inventory bounds the length of every strict parent chain. -/
def proposedAddress (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (b : BlockId Label) : List Nat :=
  (traceAddress? cfg blocks (reachableBlocks cfg blocks).length b).getD []

/-- Synthesize addresses and pass them through the existing tree certifier
for the original CFG. The label numbering serves the certifier's unreachable
addresses. -/
def synthesize? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (number : BlockId Label → Nat) (injective : Function.Injective number) :
    Option {tree : DominatorTree cfg // tree.Complete} :=
  certify? cfg blocks (proposedAddress cfg blocks) number injective

end Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis
