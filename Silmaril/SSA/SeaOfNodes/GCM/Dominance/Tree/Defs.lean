module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Defs

/-! # Checked dominator addresses for a finite typed CFG inventory -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable [DecidableEq (Target Label)]

/-- The existing reachability traversal with every vertex kept. -/
def reachableBlocks (cfg : Cfg Op Label Input Result) (blocks : List (Target Label)) :
    List (BlockId Label) :=
  reached cfg blocks (fun _ => true)

/-- Validate the root, one-step parent addresses, label uniqueness and
ancestry against computed dominance on the reachable inventory. -/
def check (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (proposed : BlockId Label → List Nat) : Bool :=
  let live := reachableBlocks cfg blocks
  checkClosed cfg blocks && decide (proposed none = []) &&
    live.all (fun b => b.isNone || (proposed b).getLast?.any fun childIndex =>
      live.any fun parent => decide (proposed b = proposed parent ++ [childIndex])) &&
    live.all (fun a => live.all fun b =>
      decide (proposed a = proposed b → a = b) &&
        decide ((proposed a).isPrefixOf (proposed b) = dominates? cfg blocks a b))

/-- Preserve reachable address lengths and reserve the initial zero for
unreachable labels. The label numbers serve only to distinguish those labels. -/
def address (live : List (BlockId Label)) (number : BlockId Label → Nat)
    (proposed : BlockId Label → List Nat) (b : BlockId Label) : List Nat :=
  if b ∈ live then (proposed b).map Nat.succ else [0, number b]

end Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree
