module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs
public import Mathlib.Logic.Embedding.Basic

/-! Embed typed addresses and extend an initialized heap with an arbitrary frame. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding

open RVSDG (Tuple)

abbrev Embedding (small large : Nat) := Address small ↪ Address large

variable {small large : Nat} {args : List ValueSort}

def restrict (e : Embedding small large) (largeHeap : Heap large) : Heap small :=
  fun a => largeHeap (e a)

/-- Take the source value on the image and the frame value elsewhere. -/
def extend (e : Embedding small large) (frame : Heap large) (source : Heap small) : Heap large :=
  fun a =>
    match (List.finRange small).find? (fun b => decide (e b = a)) with
    | some b => source b
    | none => frame a

def SameFrame (e : Embedding small large) (initial final : Heap large) : Prop :=
  ∀ a, (¬ ∃ b, e b = a) → final a = initial a

def value (e : Embedding small large) : (sort : ValueSort) → Val small sort → Val large sort
  | .address => e
  | .word => id

def input (e : Embedding small large) (values : Tuple (Val small) args) : Tuple (Val large) args :=
  values.map (value e)

def result (e : Embedding small large) (frame : Heap large) (out : Word × Heap small) : Word × Heap large :=
  (out.1, extend e frame out.2)

end Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding
