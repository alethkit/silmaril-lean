module

public import Silmaril.Semantics.RuntimeWires.Sliced.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

/-- A wire is named by its starting port. Box positions count only boxes
within a row, leaving through-wire positions out of the name. -/
inductive WireOrigin where
  | boundary (port : ℕ)
  | box (row box port : ℕ)
  deriving DecidableEq

abbrev NamedWire (O : Type u) := O × WireOrigin

/-- Associate the given labels with the successive ports. -/
def namePorts {O : Type u} (origin : ℕ → WireOrigin) (labels : List O) : List (NamedWire O) :=
  labels.zipIdx.map (fun p => (p.1, origin p.2))

structure BoxTrace {O : Type u} (S : Signature.{u,v} O) where
  generator : S.Edge
  inputs : List (NamedWire O)
  outputs : List (NamedWire O)

structure RowTrace {O : Type u} (S : Signature.{u,v} O) where
  frontier : List (NamedWire O)
  boxes : List (BoxTrace S)

structure SheetTrace {O : Type u} (S : Signature.{u,v} O) where
  rows : List (List (BoxTrace S))
  outputs : List (NamedWire O)

variable {O : Type u} {S : Signature.{u,v} O}

/-- Trace a row from its ordered named input frontier. Each through-wire
keeps its name, and each box consumes its ordered inputs and names its own outputs. -/
def Row.traceWires : {A B : List O} → Row S A B → ℕ → ℕ → List (NamedWire O) → RowTrace S
  | _, _, .empty, _, _, _ => ⟨[], []⟩
  | _, _, .wire _ r, row, boxIndex, input =>
      let rest := r.traceWires row boxIndex input.tail
      ⟨input.take 1 ++ rest.frontier, rest.boxes⟩
  | _, _, .box e r, row, boxIndex, input =>
      let ins := input.take (S.source e).length
      let outs := namePorts (.box row boxIndex) (S.target e)
      let rest := r.traceWires row (boxIndex + 1) (input.drop (S.source e).length)
      ⟨outs ++ rest.frontier, ⟨e, ins, outs⟩ :: rest.boxes⟩

/-- Trace a sheet starting at the given row number and named frontier. -/
def Sheet.traceWiresFrom : {A B : List O} → Sheet S A B → ℕ → List (NamedWire O) → SheetTrace S
  | _, _, .empty _, _, input => ⟨[], input⟩
  | _, _, .cons r p, row, input =>
      let current := r.traceWires row 0 input
      let rest := p.traceWiresFrom (row + 1) current.frontier
      ⟨current.boxes :: rest.rows, rest.outputs⟩

/-- Trace the composed sheet using only its cells and ordered input word.
An occurrence of a name at an input port or the final cap records the
wire from its named source to that port. -/
def Sheet.traceWires {A B : List O} (p : Sheet S A B) : SheetTrace S :=
  p.traceWiresFrom 0 (namePorts .boundary A)

end Silmaril.RuntimeWires.Sliced
