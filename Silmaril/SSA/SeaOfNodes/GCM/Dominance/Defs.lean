module

public import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Defs

/-! # Executable structural dominance on a finite typed CFG inventory -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Dominance

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open NaturalLoop (slots vertices)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}

/-- Project each actual successor together with its source slot. Parallel
conditional arms remain separate occurrences even at the same target. -/
def occurrences (cfg : Cfg Op Label Input Result) (src : BlockId Label) :
    List (EdgeSlot × Target Label) :=
  slots.filterMap fun slot => ((shape cfg src).target slot).map (fun dst => (slot, dst))

variable [DecidableEq (Target Label)]

/-- The entry and every listed block have all their successors represented.
The inventory may include unreachable blocks. -/
def checkClosed (cfg : Cfg Op Label Input Result) (blocks : List (Target Label)) : Bool :=
  (vertices blocks).all fun src => (occurrences cfg src).all fun edge => decide (edge.2 ∈ blocks)

/-- Adjacency for reachability. Edge-use clients can read the full occurrence list. -/
def hasEdge (cfg : Cfg Op Label Input Result) (src : BlockId Label) : BlockId Label → Bool
  | none => false
  | some dst => (occurrences cfg src).any fun edge => decide (edge.2 = dst)

/-- Fuelled form of `NaturalLoop.reverseClose`. Each successful step
removes the added candidate from the remaining inventory. -/
def boundedClose {B : Type} [DecidableEq B] (edge : B → B → Bool) :
    Nat → List B → List B → List B
  | 0, _, reached => reached
  | fuel + 1, remaining, reached =>
    match remaining.find? (fun src => reached.any (edge src)) with
    | none => reached
    | some src => boundedClose edge fuel (remaining.filter fun b => decide (b ≠ src)) (src :: reached)

/-- Reachability from the anonymous entry through admitted vertices. The
closure uses the forward CFG edges by reversing the traversal predicate. -/
def reached (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (keep : BlockId Label → Bool) : List (BlockId Label) :=
  let remaining := (blocks.map some).filter keep
  let seeds := if keep none then [none] else []
  boundedClose (fun dst src => hasEdge cfg src dst) remaining.length remaining seeds

def reachesKeeping? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (keep : BlockId Label → Bool) (b : BlockId Label) : Bool :=
  decide (b ∈ reached cfg blocks keep)

def reachable? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (b : BlockId Label) : Bool :=
  reachesKeeping? cfg blocks (fun _ => true) b

/-- Require a closed inventory and a reachable target, then test whether
deleting the proposed dominator makes the target unreachable. -/
def dominates? (cfg : Cfg Op Label Input Result) (blocks : List (Target Label))
    (a b : BlockId Label) : Bool :=
  checkClosed cfg blocks && reachable? cfg blocks b &&
    !(reachesKeeping? cfg blocks (fun v => decide (v ≠ a)) b)

end Silmaril.SSA.SeaOfNodes.GCM.Dominance
