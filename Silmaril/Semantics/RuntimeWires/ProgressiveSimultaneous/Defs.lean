module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Defs

@[expose] public section

/-!
# Isolated layers of progressive vertices

A local comparison for Definition 3.2 and Figure 7 in Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5 (pp. 9:6–9:7). Distinct x-coordinates give distinct
ordered slots even for vertices with empty ports.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable (d : Diagram S V W kind)

/-- The only vertices in this closed slab lie on its specified interior
event height. -/
structure IsolatesLayer (height lo hi : ℝ) : Prop where
  lo_inside : 0 < lo
  below : lo < height
  above : height < hi
  hi_inside : hi < 1
  only_height : ∀ j, d.vertexHeight j ∈ Set.Icc lo hi → d.vertexHeight j = height

/-- Two interior cuts enclose just the two specified vertices, at the same
height and in the given left-to-right order. -/
structure IsolatesPair (v z : Fin V) (lo hi : ℝ) : Prop where
  same_height : d.vertexHeight z = d.vertexHeight v
  left_to_right : d.vertexX v < d.vertexX z
  lo_inside : 0 < lo
  below : lo < d.vertexHeight v
  above : d.vertexHeight v < hi
  hi_inside : hi < 1
  only : ∀ j, d.vertexHeight j ∈ Set.Icc lo hi → j = v ∨ j = z

theorem IsolatesPair.toLayer {v z : Fin V} {lo hi : ℝ} (p : d.IsolatesPair v z lo hi) :
    d.IsolatesLayer (d.vertexHeight v) lo hi :=
  ⟨p.lo_inside, p.below, p.above, p.hi_inside,
    fun j hj => (p.only j hj).elim (congrArg d.vertexHeight)
      (fun he => (congrArg d.vertexHeight he).trans p.same_height)⟩

/-- Ordered passing wires, classified by their horizontal point at the event. -/
structure PassingWires (v z : Fin V) where
  left : List (Fin W)
  middle : List (Fin W)
  right : List (Fin W)
  left_exact : ∀ w, w ∈ left ↔ d.crosses w (d.vertexHeight v) ∧
    d.x w (d.vertexHeight v) < d.vertexX v
  middle_exact : ∀ w, w ∈ middle ↔ d.crosses w (d.vertexHeight v) ∧
    d.vertexX v < d.x w (d.vertexHeight v) ∧ d.x w (d.vertexHeight v) < d.vertexX z
  right_exact : ∀ w, w ∈ right ↔ d.crosses w (d.vertexHeight v) ∧
    d.vertexX z < d.x w (d.vertexHeight v)
  left_order : left.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v))
  middle_order : middle.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v))
  right_order : right.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v))

/-- The passing regions and the two incident blocks form exact ordered cuts
on both sides of the pair. -/
structure PairSlice (v z : Fin V) (lo hi : ℝ) extends d.PassingWires v z where
  isolation : d.IsolatesPair v z lo hi
  before : d.OrderedCut lo ((left ++ (d.inputs v ++ middle)) ++ (d.inputs z ++ right))
  after : d.OrderedCut hi ((left ++ (d.outputs v ++ middle)) ++ (d.outputs z ++ right))

namespace PairSlice

open Silmaril.RuntimeWires.Sliced

variable {d} {v z : Fin V} {lo hi : ℝ} (s : d.PairSlice v z lo hi)

def inputWires : List (Fin W) :=
  (s.left ++ (d.inputs v ++ s.middle)) ++ (d.inputs z ++ s.right)

def outputWires : List (Fin W) :=
  (s.left ++ (d.outputs v ++ s.middle)) ++ (d.outputs z ++ s.right)

def leftRow : Row S
    (s.left.map d.label ++ (S.source (d.generator v) ++ s.middle.map d.label))
    (s.left.map d.label ++ (S.target (d.generator v) ++ s.middle.map d.label)) :=
  Row.pass (s.left.map d.label)
    (.box (d.generator v) (Row.straight (s.middle.map d.label)))

def rightRow : Row S (S.source (d.generator z) ++ s.right.map d.label)
    (S.target (d.generator z) ++ s.right.map d.label) :=
  .box (d.generator z) (Row.straight (s.right.map d.label))

/-- The boundary word read from the incoming blocks in their common order. -/
def sourceWord : List O :=
  (s.left.map d.label ++ (S.source (d.generator v) ++ s.middle.map d.label)) ++
    (S.source (d.generator z) ++ s.right.map d.label)

/-- The boundary word read from the outgoing blocks in their common order. -/
def targetWord : List O :=
  (s.left.map d.label ++ (S.target (d.generator v) ++ s.middle.map d.label)) ++
    (S.target (d.generator z) ++ s.right.map d.label)

/-- Perform the left vertex first, carrying the right slot past it. -/
def leftFirst : Sheet S s.sourceWord s.targetWord :=
  .cons (s.leftRow.beside (Row.straight _))
    (.cons (Row.pass _ s.rightRow) (.empty _))

/-- Perform the right vertex first, carrying the left slot past it. -/
def rightFirst : Sheet S s.sourceWord s.targetWord :=
  .cons (Row.pass _ s.rightRow)
    (.cons (s.leftRow.beside (Row.straight _)) (.empty _))

end PairSlice

/-- A cell at the event height is a passing wire or a point vertex. -/
abbrev LayerSlot (V W : ℕ) := Fin W ⊕ Fin V

def slotX (height : ℝ) : LayerSlot V W → ℝ
  | .inl w => d.x w height
  | .inr j => d.vertexX j

def atLayer (height : ℝ) : LayerSlot V W → Prop
  | .inl w => d.crosses w height
  | .inr j => d.vertexHeight j = height

def slotInputs : LayerSlot V W → List (Fin W) := Sum.elim List.singleton d.inputs

def slotOutputs : LayerSlot V W → List (Fin W) := Sum.elim List.singleton d.outputs

def slotSource : LayerSlot V W → List O
  | .inl w => [d.label w]
  | .inr j => S.source (d.generator j)

def slotTarget : LayerSlot V W → List O
  | .inl w => [d.label w]
  | .inr j => S.target (d.generator j)

/-- Read a row from its ordered cells. Each vertex, including a scalar,
contributes a generator cell. -/
def layerRow : (slots : List (LayerSlot V W)) →
    Sliced.Row S (slots.flatMap d.slotSource) (slots.flatMap d.slotTarget)
  | [] => .empty
  | .inl w :: tail => .wire (d.label w) (layerRow tail)
  | .inr j :: tail => .box (d.generator j) (layerRow tail)

/-- One horizontal layer of a drawing, with the complete ordered cell list
and the exact ordered wire decompositions at both cuts. -/
structure LayerSlice (height lo hi : ℝ) where
  isolation : d.IsolatesLayer height lo hi
  slots : List (LayerSlot V W)
  exact_slots : ∀ c, c ∈ slots ↔ d.atLayer height c
  ordered : slots.Pairwise (fun a b => d.slotX height a < d.slotX height b)
  before : d.OrderedCut lo (slots.flatMap d.slotInputs)
  after : d.OrderedCut hi (slots.flatMap d.slotOutputs)

namespace LayerSlice

variable {d} {height lo hi : ℝ} (s : d.LayerSlice height lo hi)

/-- The layer's vertices in strict horizontal order. -/
def vertices : List (Fin V) := s.slots.filterMap Sum.getRight?

def row : Sliced.Row S (s.slots.flatMap d.slotSource) (s.slots.flatMap d.slotTarget) :=
  d.layerRow s.slots

end LayerSlice

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
