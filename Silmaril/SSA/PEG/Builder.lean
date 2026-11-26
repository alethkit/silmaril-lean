module

public import Silmaril.SSA.PEG.Defs

/-! # Checking a numbered PEG table

Labels here already carry their declared opcode profiles and parameter ports.
The checker checks raw vertex numbers, operand arity and sorts, including
the ordered result boundary. Forward references are allowed. Loop parents
and graph scope are checked by separate predicates in `Scope`.
-/

@[expose] public section

namespace Silmaril.SSA.PEG

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {n l : Nat} {sort : Fin n → Ty Data}
variable {P : InstructionSet.{u,v} Data} {params results : List (Ty Data)}

/-- Read an untyped vertex number against an expected sort. -/
def Ref.check [DecidableEq Data] (sort : Fin n → Ty Data) (expected : Ty Data)
    (i : Nat) : Option (Ref sort expected) :=
  if bounded : i < n then
    if typed : sort ⟨i, bounded⟩ = expected then some ⟨⟨i, bounded⟩, typed⟩ else none
  else none

/-- Serialize the ordered vertex references, retaining repeated operands. -/
def refNumbers : {ts : List (Ty Data)} → Tuple (Ref sort) ts → List Nat
  | _, .nil => []
  | _, .cons r rs => r.id.val :: refNumbers rs

def checkRefs [DecidableEq Data] (sort : Fin n → Ty Data) :
    (ts : List (Ty Data)) → List Nat → Option (Tuple (Ref sort) ts)
  | [], [] => some .nil
  | t :: ts, i :: is =>
    match Ref.check sort t i with
    | none => none
    | some r => (checkRefs sort ts is).map (.cons r)
  | _, _ => none

structure RawNode (P : InstructionSet.{u,v} Data) (params : List (Ty Data)) (loops : Nat)
    (out : Ty Data) where
  inputs : List (Ty Data)
  label : Label P params (Fin loops) inputs out
  args : List Nat

structure RawGraph (P : InstructionSet.{u,v} Data) (params results : List (Ty Data))
    (nodes loops : Nat) where
  forest : LoopForest loops
  sort : Fin nodes → Ty Data
  node : (i : Fin nodes) → RawNode P params loops (sort i)
  roots : List Nat

/-- Build a finite table after checking each row and the root list. -/
def RawGraph.check [DecidableEq Data] (raw : RawGraph P params results n l) :
    Option (Graph P params results n l) :=
  match checkRefs raw.sort results raw.roots with
  | none => none
  | some roots =>
    if ok : ∀ i, (checkRefs raw.sort (raw.node i).inputs (raw.node i).args).isSome then
      some ⟨raw.forest, raw.sort, fun i =>
        (Node.ofLabel (raw.node i).label
          ((checkRefs raw.sort (raw.node i).inputs (raw.node i).args).get (ok i))), roots⟩
    else none

def Graph.toRaw (g : Graph P params results n l) : RawGraph P params results n l where
  forest := g.forest
  sort := g.sort
  node i := ⟨(g.node i).inputs, (g.node i).label, refNumbers (g.node i).args⟩
  roots := refNumbers g.roots

end Silmaril.SSA.PEG
