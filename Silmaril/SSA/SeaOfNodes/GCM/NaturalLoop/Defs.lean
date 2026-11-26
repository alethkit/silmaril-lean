module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Defs

/-! # Checked membership and placement for one natural loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- A proposed backedge identifies one actual successor occurrence of the latch. -/
structure Backedge (Label : List Width → Type) where
  header : Target Label
  latch : Target Label
  slot : EdgeSlot

def vertices (blocks : List (Target Label)) : List (BlockId Label) := none :: blocks.map some

def slots : List EdgeSlot := [.jump, .onTrue, .onFalse]

/-- Compare the existing typed block IDs via the certificate's injective addresses. -/
def blockDecEq (tree : DominatorTree cfg) : DecidableEq (BlockId Label) :=
  fun a b => if same : tree.address a = tree.address b then
    isTrue (tree.address_injective same)
  else isFalse (fun eq => same (congrArg tree.address eq))

/-- Require the inventory to contain exactly reachable blocks, allowing
duplicate names. Every outgoing occurrence from the inventory stays in it. -/
def checkInventory (tree : DominatorTree cfg) (blocks : List (Target Label)) : Bool :=
  letI := blockDecEq tree
  let all := vertices blocks
  all.all fun src => tree.reachable src && slots.all fun slot =>
    match (shape cfg src).target slot with
    | none => true
    | some dst => decide (some dst ∈ all)

def checkBackedge (tree : DominatorTree cfg) (blocks : List (Target Label)) (edge : Backedge Label) :
    Bool :=
  letI := blockDecEq tree
  let header := some edge.header
  let latch := some edge.latch
  checkInventory tree blocks &&
    (decide (header ∈ vertices blocks) && decide (latch ∈ vertices blocks)) &&
    (decide ((shape cfg latch).target edge.slot = header) &&
      (tree.address header).isPrefixOf (tree.address latch))

/-- Actual CFG adjacency with the occurrence hidden. Absent slots do not
target the anonymous entry. -/
def edge? (tree : DominatorTree cfg) (src : BlockId Label) : BlockId Label → Bool
  | none => false
  | some dst =>
    letI := blockDecEq tree
    slots.any fun slot => decide ((shape cfg src).target slot = some dst)

/-- A path among reachable blocks to the latch with the header omitted. -/
inductive ToLatch (cfg : Cfg Op Label Input Result) (edge : Backedge Label) :
    BlockId Label → Prop where
  | latch (reachable : Reachable cfg (some edge.latch)) (avoids : edge.latch ≠ edge.header) :
      ToLatch cfg edge (some edge.latch)
  | predecessor {src : BlockId Label} {dst : Target Label}
      (reachable : Reachable cfg src) (avoids : src ≠ some edge.header)
      (slot : EdgeSlot) (actual : (shape cfg src).target slot = some dst)
      (tail : ToLatch cfg edge (some dst)) : ToLatch cfg edge src

def Member (cfg : Cfg Op Label Input Result) (edge : Backedge Label) (b : BlockId Label) : Prop :=
  b = some edge.header ∨ ToLatch cfg edge b

/-- Add a predecessor of the current set until the remaining list contains
none. Removing all occurrences of the selected predecessor bounds the recursion. -/
def reverseClose {B : Type} [DecidableEq B] (hasEdge : B → B → Bool)
    (remaining reached : List B) : List B :=
  match _found : remaining.find? (fun src => reached.any (hasEdge src)) with
  | none => reached
  | some src => reverseClose hasEdge (remaining.filter (fun b => decide (b ≠ src))) (src :: reached)
termination_by remaining.length
decreasing_by
  have smaller : (remaining.filter (fun b => decide (b ≠ src))).length < remaining.length :=
    List.length_filter_lt_length_iff_exists.mpr
      ⟨src, List.mem_of_find?_eq_some _found, by simp⟩
  rw [List.unattach_filter (g := fun b => decide (b ≠ src)) (hf := fun _ _ => rfl),
    List.unattach_attach]
  exact smaller

/-- Stop the reverse traversal at the header. A self-backedge has just
the header as its member. -/
def members (tree : DominatorTree cfg) (blocks : List (Target Label)) (edge : Backedge Label) :
    List (BlockId Label) :=
  letI := blockDecEq tree
  let header := some edge.header
  let latch := some edge.latch
  let remaining := (vertices blocks).filter fun b => decide (b ≠ header ∧ b ≠ latch)
  let seeds := if latch = header then [] else [latch]
  header :: reverseClose (edge? tree) remaining seeds

def checkedMembers? (tree : DominatorTree cfg) (blocks : List (Target Label)) (edge : Backedge Label) :
    Option (List (BlockId Label)) :=
  if checkBackedge tree blocks edge then some (members tree blocks edge) else none

/-- Contribution of this one natural loop to nesting depth. -/
def depth (tree : DominatorTree cfg) (loopMembers : List (BlockId Label)) (b : BlockId Label) : Nat :=
  letI := blockDecEq tree
  if b ∈ loopMembers then 1 else 0

/-- Feed the derived single-loop depth into the existing checked placement ranking. -/
def choosePlacement (tree : DominatorTree cfg) (blocks : List (Target Label)) (edge : Backedge Label)
    (operands : List (Point Label)) (uses : List (Use Label)) : Option (Point Label) := do
  let loopMembers ← checkedMembers? tree blocks edge
  chooseLoopPlacement tree (depth tree loopMembers) blocks operands uses

end Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop
