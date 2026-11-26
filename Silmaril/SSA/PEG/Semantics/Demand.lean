module

public import Silmaril.SSA.PEG.Defs

/-! # Evaluation demands and finite rank certificates -/

@[expose] public section

namespace Silmaril.SSA.PEG

universe u v

/-- An iteration count for every loop in the frame. -/
abbrev Index (loops : Nat) := Fin loops → Nat

def Index.set {loops : Nat} (i : Index loops) (l : Fin loops) (k : Nat) : Index loops :=
  fun j => if j = l then k else i j

/-- How an operand can change the iteration vector. A sampling edge admits
every count in the specified coordinate, covering both the chosen count and
all prefix queries. Both φ arms are conservatively included. -/
def EdgeKind.Changes {loops : Nat} : EdgeKind (Fin loops) → Index loops → Index loops → Prop
  | .ordinary, i, j => j = i
  | .initial l, i, j => i l = 0 ∧ j = i
  | .feedback l, i, j => ∃ k, i l = k + 1 ∧ j = i.set l k
  | .sample l, i, j => ∃ k, j = i.set l k
  | .index _, i, j => j = i

abbrev Request (nodes loops : Nat) := Fin nodes × Index loops

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

/-- The smaller request demands a child of the larger request. -/
def Graph.Demand (g : Graph P params results n l) (child parent : Request n l) : Prop :=
  ∃ kind, g.Edge parent.1 kind child.1 ∧ kind.Changes parent.2 child.2

/-- Components of a finite lexicographic ranking, most significant first.
Vertex phases can precede, follow, or separate iteration counters. -/
inductive RankComponent (nodes loops : Nat) where
  | phase (rank : Fin nodes → Nat)
  | counter (loop : Fin loops)

abbrev DemandRank (nodes loops : Nat) := List (RankComponent nodes loops)

inductive RankChange where
  | lower
  | equal
  | unknown
  deriving DecidableEq

def RankComponent.value (c : RankComponent n l) (q : Request n l) : Nat :=
  match c with
  | .phase rank => rank q.1
  | .counter loop => q.2 loop

/-- An edge-local test valid uniformly over the unbounded iteration space. -/
def RankComponent.change (c : RankComponent n l) (a b : Fin n) (kind : EdgeKind (Fin l)) :
    RankChange :=
  match c with
  | .phase rank =>
    if rank b < rank a then .lower else if rank b = rank a then .equal else .unknown
  | .counter loop =>
    match kind with
    | .feedback k => if loop = k then .lower else .equal
    | .sample k => if loop = k then .unknown else .equal
    | _ => .equal

def DemandRank.checkEdge : DemandRank n l → Fin n → Fin n → EdgeKind (Fin l) → Bool
  | [], _, _, _ => false
  | c :: cs, a, b, kind =>
    match c.change a b kind with
    | .lower => true
    | .equal => checkEdge cs a b kind
    | .unknown => false

/-- Check all ordered operand occurrences. A component must strictly decrease
after a prefix of unchanged components. Components after that are unrestricted. -/
def DemandRank.check (rank : DemandRank n l) (g : Graph P params results n l) : Bool :=
  (List.finRange n).all fun a =>
    let node := g.node a
    (List.finRange node.inputs.length).all fun slot =>
      rank.checkEdge a (node.arg slot).id (node.label.kind slot)

end Silmaril.SSA.PEG
