module

public import Silmaril.Semantics.RuntimeWires.SlicedTrace.Defs

@[expose] public section

/-!
# Structural incidence under a seam split

This compares decoding at different slicings in the combinatorial setting
of Definition 3.2, Figure 7 and Lemma 3.4 (pp. 9:6–9:7) of Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Sliced

universe u v

/-- A row number and a horizontal box ordinal within that row. -/
abbrev BoxAddress := ℕ × ℕ

variable {O : Type u} {S : Signature.{u,v} O}

def WireOrigin.rename (route : BoxAddress → BoxAddress) : WireOrigin → WireOrigin
  | .boundary port => .boundary port
  | .box row ordinal port => let dest := route (row, ordinal); .box dest.1 dest.2 port

def NamedWire.rename (route : BoxAddress → BoxAddress) (wire : NamedWire O) : NamedWire O :=
  (wire.1, wire.2.rename route)

def BoxTrace.rename (route : BoxAddress → BoxAddress) (box : BoxTrace S) : BoxTrace S :=
  ⟨box.generator, box.inputs.map (NamedWire.rename route), box.outputs.map (NamedWire.rename route)⟩

abbrev BoxOccurrence (S : Signature.{u,v} O) := BoxAddress × BoxTrace S

def BoxOccurrence.rename (route : BoxAddress → BoxAddress) (box : BoxOccurrence S) : BoxOccurrence S :=
  (route box.1, box.2.rename route)

/-- Address the box records in one row. Through cells have no box ordinal. -/
def addressBoxes (row : ℕ) : ℕ → List (BoxTrace S) → List (BoxOccurrence S)
  | _, [] => []
  | box, trace :: rest => ((row, box), trace) :: addressBoxes row (box + 1) rest

/-- The two new rows traced from their shared input frontier. -/
def traceSplitRows {A M B : List O} (p : Row S A M) (q : Row S M B)
    (row upper lower : ℕ) (input : List (NamedWire O)) :
    List (NamedWire O) × List (BoxOccurrence S) :=
  let first := p.traceWires row upper input
  let second := q.traceWires (row + 1) lower first.frontier
  (second.frontier, addressBoxes row upper first.boxes ++ addressBoxes (row + 1) lower second.boxes)

/-- A list of destinations indexed by consecutive original box ordinals. -/
def RoutesBoxes (route : BoxAddress → BoxAddress) (row first : ℕ) (destinations : List BoxAddress) :
    Prop :=
  ∀ i (h : i < destinations.length), route (row, first + i) = destinations[i]

/-- The address map for splitting one row. Earlier rows keep their
addresses and later rows move down by one. -/
def splitRoute (row : ℕ) (destinations : List BoxAddress) (position : BoxAddress) : BoxAddress :=
  if position.1 < row then position
  else if position.1 = row then destinations[position.2]?.getD position
  else (position.1 + 1, position.2)

/-- Address a decoded sheet transcript, with row offsets for partial sheets. -/
def addressRows : ℕ → List (List (BoxTrace S)) → List (BoxOccurrence S)
  | _, [] => []
  | row, boxes :: rest => addressBoxes row 0 boxes ++ addressRows (row + 1) rest

def SheetTrace.occurrences (trace : SheetTrace S) : List (BoxOccurrence S) :=
  addressRows 0 trace.rows

def SheetTrace.boxAddresses (trace : SheetTrace S) : Set BoxAddress :=
  {address | address ∈ trace.occurrences.map Prod.fst}

/-- Exact correspondence of decoded incidence under a routing of boxes.
The permutation concerns addressed occurrences. The input and output
lists inside each box and the outer output list keep their port order. -/
structure SheetTrace.RenamedAt (left right : SheetTrace S) (route : BoxAddress → BoxAddress)
    (leftRow rightRow : ℕ) : Prop where
  occurrences : ((addressRows leftRow left.rows).map (BoxOccurrence.rename route)).Perm
    (addressRows rightRow right.rows)
  outputs : left.outputs.map (NamedWire.rename route) = right.outputs

abbrev SheetTrace.Renamed (left right : SheetTrace S) (route : BoxAddress → BoxAddress) : Prop :=
  left.RenamedAt right route 0 0

end Silmaril.RuntimeWires.Sliced
