module

public import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Defs

/-! # Discover and coalesce natural loops on the validated typed CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopForest

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open NaturalLoop (Backedge blockDecEq checkInventory slots)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- A backedge is a reachable CFG occurrence whose target dominates its source. -/
def ActualBackedge (cfg : Cfg Op Label Input Result) (edge : Backedge Label) : Prop :=
  Reachable cfg (some edge.latch) ∧
    (shape cfg (some edge.latch)).target edge.slot = some edge.header ∧
    Dominates cfg (some edge.header) (some edge.latch)

def targetDecEq (tree : DominatorTree cfg) : DecidableEq (Target Label) :=
  letI := blockDecEq tree
  fun a b => decidable_of_iff (some a = some b) Option.some_inj

/-- Scan each named latch once, retaining the exact slot even when two slots
target one header. The anonymous entry cannot be a latch because it has no incoming edge. -/
def scan (tree : DominatorTree cfg) (blocks : List (Target Label)) : List (Backedge Label) :=
  letI := targetDecEq tree
  blocks.eraseDups.flatMap fun latch => slots.filterMap fun slot => do
    let header ← (shape cfg (some latch)).target slot
    if (tree.address (some header)).isPrefixOf (tree.address (some latch)) then
      some ⟨header, latch, slot⟩
    else none

def discover? (tree : DominatorTree cfg) (blocks : List (Target Label)) :
    Option (List (Backedge Label)) :=
  if checkInventory tree blocks then some (scan tree blocks) else none

structure HeaderLoop (Label : List Width → Type) where
  header : Target Label
  members : List (BlockId Label)

/-- Union the per-occurrence member sets before counting loops. -/
def coalesce (tree : DominatorTree cfg) (blocks : List (Target Label))
    (edges : List (Backedge Label)) : List (HeaderLoop Label) :=
  letI := targetDecEq tree
  letI := blockDecEq tree
  (edges.map Backedge.header).eraseDups.map fun header =>
    let incoming := edges.filter fun edge => decide (edge.header = header)
    ⟨header, (incoming.flatMap (NaturalLoop.members tree blocks)).eraseDups⟩

def loops? (tree : DominatorTree cfg) (blocks : List (Target Label)) :
    Option (List (HeaderLoop Label)) :=
  (discover? tree blocks).map (coalesce tree blocks)

def StrictInside (a b : HeaderLoop Label) : Prop :=
  (∀ node ∈ a.members, node ∈ b.members) ∧ ∃ node ∈ b.members, node ∉ a.members

def Compatible (a b : HeaderLoop Label) : Prop :=
  (∀ node ∈ a.members, node ∉ b.members) ∨ StrictInside a b ∨ StrictInside b a

/-- Admit disjoint or strictly nested member sets. Crossing or coincident
sets at distinct headers are outside this forest profile. -/
def checkLaminar (tree : DominatorTree cfg) (loops : List (HeaderLoop Label)) : Bool :=
  letI := blockDecEq tree
  letI : DecidableRel (Compatible : HeaderLoop Label → HeaderLoop Label → Prop) := fun a b => by
    unfold Compatible StrictInside
    infer_instance
  decide (loops.Pairwise Compatible)

def forest? (tree : DominatorTree cfg) (blocks : List (Target Label)) :
    Option (List (HeaderLoop Label)) := do
  let loops ← loops? tree blocks
  if checkLaminar tree loops then some loops else none

def enclosing (tree : DominatorTree cfg) (loops : List (HeaderLoop Label))
    (b : BlockId Label) : List (HeaderLoop Label) :=
  letI := blockDecEq tree
  loops.filter fun loop => decide (b ∈ loop.members)

/-- The length of the chain of distinct header loops containing this block
in an admitted forest. -/
def depth (tree : DominatorTree cfg) (loops : List (HeaderLoop Label)) (b : BlockId Label) : Nat :=
  (enclosing tree loops b).length

def choosePlacement (tree : DominatorTree cfg) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) : Option (Point Label) := do
  let loops ← forest? tree blocks
  chooseLoopPlacement tree (depth tree loops) blocks operands uses

end Silmaril.SSA.SeaOfNodes.GCM.LoopForest
