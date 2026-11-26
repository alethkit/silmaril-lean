module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-!
# One structural refinement round for loop-carried producers

The graph has one implicit Loop Region. Each Phi enters from a function
argument and reads its feedback operand on the backedge. Pure producers
read arguments or earlier vertices in the current activation. Only feedback
can close a cycle.

The seed partitions producers by typed opcode or Phi profile. Argument
positions are distinguished throughout. Refinement splits classes by the
current classes of operands in occurrence order, following Click's Rice
dissertation §§4.1–4.2. See `docs/projects/sea-of-nodes-gvn-cyclic.md`.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic

open Diamond (Signature ValueSort)
open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data} {n : Nat}

/-- A typed operand in the finite producer graph. -/
inductive Source (inputs : List (ValueSort Data)) (sorts : Fin n → ValueSort Data)
    (out : ValueSort Data) where
  | argument (port : Port inputs out)
  | producer (vertex : Fin n) (typed : sorts vertex = out)

/-- Operand position in the signature of a node. Producer addresses are
replaced by class labels during refinement, while argument addresses stay
distinguished from each other and from producers. -/
inductive Address (Kind : Type u) (n : Nat) where
  | argument (sort : Kind) (position : Nat)
  | producer (sort : Kind) (vertex : Fin n)
  deriving DecidableEq

variable {inputs : List (ValueSort Data)} {sorts : Fin n → ValueSort Data}
variable {out : ValueSort Data}

def Source.address : Source inputs sorts out → Address (ValueSort Data) n
  | .argument port => .argument out port.index
  | .producer vertex _ => .producer out vertex

def Address.relabel {Kind : Type u} (classes : Fin n → Fin n) : Address Kind n → Address Kind n
  | .argument sort position => .argument sort position
  | .producer sort vertex => .producer sort (classes vertex)

/-- Erase the dependent tuple indices while keeping each occurrence's type and address. -/
def Source.addresses {ins : List (ValueSort Data)} :
    Tuple (Source inputs sorts) ins → List (Address (ValueSort Data) n)
  | .nil => []
  | .cons head tail => head.address :: addresses tail

/-- Phis have an entry operand from the argument list and a feedback
operand from the current activation. Pure operands follow signature order. -/
inductive Node (Op : Signature.{u,v} Data) (inputs : List (ValueSort Data))
    (sorts : Fin n → ValueSort Data) (out : ValueSort Data) where
  | phi (entry : Port inputs out) (backedge : Source inputs sorts out)
  | pure {ins : List (ValueSort Data)} (opcode : Op ins out) (operands : Tuple (Source inputs sorts) ins)

/-- A seed distinguishes Phis from primitives and keeps the full typed
primitive profile, including the opcode. -/
abbrev Profile (Op : Signature.{u,v} Data) :=
  ValueSort Data ⊕ (Σ ins : List (ValueSort Data), Σ out : ValueSort Data, Op ins out)

def Node.profile : Node Op inputs sorts out → Profile Op
  | .phi .. => .inl out
  | .pure opcode _ => .inr ⟨_, out, opcode⟩

/-- Entry precedes backedge, as in the two columns of `Loop.Graph.phiInputs`.
Neither this order nor primitive operand order is quotiented by permutation. -/
def Node.addresses : Node Op inputs sorts out → List (Address (ValueSort Data) n)
  | .phi entry backedge => [.argument out entry.index, backedge.address]
  | .pure _ operands => Source.addresses operands

def Node.isPure : Node Op inputs sorts out → Bool
  | .phi .. => false
  | .pure .. => true

/-- A typed producer view of one loop, restricted to direct argument entry
operands. The order certifies that pure producers have no instantaneous cycle. -/
structure Graph (Op : Signature.{u,v} Data) (inputs : List (ValueSort Data))
    (sorts : Fin n → ValueSort Data) where
  node (i : Fin n) : Node Op inputs sorts (sorts i)
  ordered (i j : Fin n) (sort : ValueSort Data) :
    (node i).isPure = true → .producer sort j ∈ (node i).addresses → j < i

abbrev Partition (n : Nat) := Fin n → Fin n

def Graph.operandClasses (g : Graph Op inputs sorts) (p : Partition n) (i : Fin n) :
    List (Address (ValueSort Data) n) :=
  (g.node i).addresses.map (Address.relabel p)

/-- Stability means that members of a class have equal profiles and equal
operand classes at every ordered occurrence. -/
def Stable (g : Graph Op inputs sorts) (p : Partition n) : Prop :=
  ∀ i j, p i = p j →
    (g.node i).profile = (g.node j).profile ∧ g.operandClasses p i = g.operandClasses p j

section Executable

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Use the first vertex with the same key as the class label. -/
def classesOf {Key : Type w} [DecidableEq Key] (key : Fin n → Key) : Partition n :=
  fun i => ((List.finRange n).find? (fun j => decide (key i = key j))).getD i

def seed (g : Graph Op inputs sorts) : Partition n :=
  classesOf (fun i => (g.node i).profile)

/-- The old label and the structural data examined by a refinement round. -/
structure RoundKey (Op : Signature.{u,v} Data) (n : Nat) where
  previous : Fin n
  profile : Profile Op
  operands : List (Address (ValueSort Data) n)

instance : DecidableEq (RoundKey Op n) := fun left right =>
  decidable_of_iff
    (left.previous = right.previous ∧ left.profile = right.profile ∧ left.operands = right.operands)
    (by cases left; cases right; simp)

/-- Perform one synchronous refinement round. Including the old label
prevents a round from merging any two old classes. -/
def refine (g : Graph Op inputs sorts) (p : Partition n) : Partition n :=
  classesOf (fun i => (⟨p i, (g.node i).profile, g.operandClasses p i⟩ : RoundKey Op n))

/-- Check structural stability of a supplied labeling by comparing all pairs
of vertices. The check accepts stable labelings regardless of their numbering. -/
def checkStable (g : Graph Op inputs sorts) (p : Partition n) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun j =>
      decide (p i = p j →
        (g.node i).profile = (g.node j).profile ∧ g.operandClasses p i = g.operandClasses p j)

end Executable

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic
