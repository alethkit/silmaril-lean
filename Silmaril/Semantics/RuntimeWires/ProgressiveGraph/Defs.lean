module

public import Silmaril.Semantics.RuntimeWires.Sliced.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# Finite progressive polygonal graphs

An independent point-vertex model for Definition 3.2 of Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5, pp. 9:6–9:7. Height increases in execution order.
The geometric data do not include a layering or a seam equivalence.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v

/-- A polygonal edge parameterized directly by height. Its planar point at
height `h` is `(x h, h)`. Only heights between its endpoints are used. -/
structure Wire (low high : ℝ) where
  x : ℝ → ℝ
  increasing : low < high
  continuous : ContinuousOn x (Set.Icc low high)
  /-- Between any two heights with no breakpoint strictly between them,
  the horizontal coordinate follows the chord joining those heights. -/
  polygonal : ∃ knots : Finset ℝ, ∀ a ∈ Set.Icc low high, ∀ b ∈ Set.Icc low high,
    a < b → (∀ k ∈ knots, k ∉ Set.Ioo a b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
    x ((1 - t) * a + t * b) = (1 - t) * x a + t * x b

namespace Wire

variable {low high : ℝ}

def point (w : Wire low high) (h : ℝ) : ℝ × ℝ := (w.x h, h)

def trace (w : Wire low high) : Set (ℝ × ℝ) := w.point '' Set.Icc low high

theorem height_strict (w : Wire low high) : StrictMono (fun h => (w.point h).2) :=
  fun _ _ h => h

end Wire

/-- The height of an endpoint. A missing vertex denotes the corresponding outer cap. -/
def endpointHeight {n : ℕ} (height : Fin n → ℝ) (cap : ℝ) (endpoint : Option (Fin n)) : ℝ :=
  endpoint.elim cap height

/-- The finite sweep uses distinct heights. The local geometry also
allows vertices at distinct points on the same horizontal line. -/
inductive VertexSeparation
  | height
  | point

def VertexSeparation.Valid (kind : VertexSeparation) {V : ℕ}
    (x height : Fin V → ℝ) : Prop :=
  match kind with
  | .height => Function.Injective height
  | .point => Function.Injective (fun v => (x v, height v))

/-- A finite drawing in the unit square. Wires can share a point only at
common incident vertices. Port numbering records the geometry of incident
ends on each side of a vertex, including their labels. -/
structure Diagram {O : Type u} (S : Signature.{u,v} O) (vertices wires : ℕ)
    (kind : VertexSeparation := .height) where
  vertexX : Fin vertices → ℝ
  vertexHeight : Fin vertices → ℝ
  vertex_inside : ∀ v, vertexX v ∈ Set.Ioo 0 1 ∧ vertexHeight v ∈ Set.Ioo 0 1
  vertex_separation : kind.Valid vertexX vertexHeight
  generator : Fin vertices → S.Edge
  label : Fin wires → O
  start : Fin wires → Option (Fin vertices)
  finish : Fin wires → Option (Fin vertices)
  wire : ∀ w, Wire (endpointHeight vertexHeight 0 (start w))
    (endpointHeight vertexHeight 1 (finish w))
  wire_inside : ∀ w, ∀ h ∈ Set.Icc (endpointHeight vertexHeight 0 (start w))
    (endpointHeight vertexHeight 1 (finish w)), (wire w).x h ∈ Set.Ioo 0 1
  start_attached : ∀ w v, start w = some v → (wire w).x (vertexHeight v) = vertexX v
  finish_attached : ∀ w v, finish w = some v → (wire w).x (vertexHeight v) = vertexX v
  /-- No wire interior meets another wire, including its endpoints. -/
  separated : ∀ {w z}, w ≠ z → ∀ {h},
    h ∈ Set.Ioo (endpointHeight vertexHeight 0 (start w)) (endpointHeight vertexHeight 1 (finish w)) →
    h ∈ Set.Icc (endpointHeight vertexHeight 0 (start z)) (endpointHeight vertexHeight 1 (finish z)) →
    (wire w).x h ≠ (wire z).x h
  avoids_vertex : ∀ w v, vertexHeight v ∈ Set.Ioo (endpointHeight vertexHeight 0 (start w))
    (endpointHeight vertexHeight 1 (finish w)) → (wire w).x (vertexHeight v) ≠ vertexX v
  input_boundary_separated : ∀ {w z}, w ≠ z → start w = none → start z = none →
    (wire w).x 0 ≠ (wire z).x 0
  output_boundary_separated : ∀ {w z}, w ≠ z → finish w = none → finish z = none →
    (wire w).x 1 ≠ (wire z).x 1
  input : ∀ v, Fin (S.source (generator v)).length → Fin wires
  output : ∀ v, Fin (S.target (generator v)).length → Fin wires
  input_exact : ∀ v w, finish w = some v ↔ ∃ i, input v i = w
  output_exact : ∀ v w, start w = some v ↔ ∃ i, output v i = w
  input_types : ∀ v, (List.ofFn (input v)).map label = S.source (generator v)
  output_types : ∀ v, (List.ofFn (output v)).map label = S.target (generator v)
  /-- Order the incident input ends using their horizontal positions on the
  common part of their open height intervals. -/
  input_order : ∀ v {i j}, i < j → ∀ {h},
    endpointHeight vertexHeight 0 (start (input v i)) < h →
    endpointHeight vertexHeight 0 (start (input v j)) < h → h < vertexHeight v →
    (wire (input v i)).x h < (wire (input v j)).x h
  /-- Order the incident output ends on the other side of the vertex. -/
  output_order : ∀ v {i j}, i < j → ∀ {h},
    vertexHeight v < h → h < endpointHeight vertexHeight 1 (finish (output v i)) →
    h < endpointHeight vertexHeight 1 (finish (output v j)) →
    (wire (output v i)).x h < (wire (output v j)).x h

namespace Diagram

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}

theorem distinct_heights (d : Diagram S V W) : Function.Injective d.vertexHeight :=
  d.vertex_separation

variable {kind : VertexSeparation} (d : Diagram S V W kind)

def lower (w : Fin W) : ℝ := endpointHeight d.vertexHeight 0 (d.start w)
def upper (w : Fin W) : ℝ := endpointHeight d.vertexHeight 1 (d.finish w)
def x (w : Fin W) (h : ℝ) : ℝ := (d.wire w).x h

def crosses (w : Fin W) (h : ℝ) : Prop := h ∈ Set.Ioo (d.lower w) (d.upper w)
def covers (w : Fin W) (h : ℝ) : Prop := h ∈ Set.Icc (d.lower w) (d.upper w)

def inputs (v : Fin V) : List (Fin W) := List.ofFn (d.input v)
def outputs (v : Fin V) : List (Fin W) := List.ofFn (d.output v)

/-- Two interior cuts bound an interval containing just the specified vertex,
with neither endpoint at a vertex height. -/
structure Isolates (v : Fin V) (lo hi : ℝ) : Prop where
  lo_inside : 0 < lo
  below : lo < d.vertexHeight v
  above : d.vertexHeight v < hi
  hi_inside : hi < 1
  only : ∀ z, d.vertexHeight z ∈ Set.Icc lo hi → z = v

/-- An interior height distinct from all vertex heights. -/
structure Regular (h : ℝ) : Prop where
  inside : h ∈ Set.Ioo 0 1
  avoids : ∀ v, d.vertexHeight v ≠ h

def wireTrace : Set (ℝ × ℝ) := ⋃ w, (d.wire w).trace

/-- A geometric cut lists each wire crossing the chosen height once and in
strict left-to-right order. -/
structure OrderedCut (h : ℝ) (wires : List (Fin W)) : Prop where
  exact_wires : ∀ w, w ∈ wires ↔ d.crosses w h
  ordered : wires.Pairwise (fun a b => d.x a h < d.x b h)

/-- A single-event reconstruction. The shared lists contain the exact wire
identities that pass to the left and to the right of the vertex. -/
structure EventSlice (v : Fin V) (lo hi : ℝ) where
  left : List (Fin W)
  right : List (Fin W)
  left_exact : ∀ w, w ∈ left ↔ d.crosses w (d.vertexHeight v) ∧
    d.x w (d.vertexHeight v) < d.vertexX v
  right_exact : ∀ w, w ∈ right ↔ d.crosses w (d.vertexHeight v) ∧
    d.vertexX v < d.x w (d.vertexHeight v)
  before : d.OrderedCut lo (left ++ d.inputs v ++ right)
  after : d.OrderedCut hi (left ++ d.outputs v ++ right)

namespace EventSlice

variable {d} {v : Fin V} {lo hi : ℝ} (s : d.EventSlice v lo hi)

def beforeWires : List (Fin W) := s.left ++ d.inputs v ++ s.right

def afterWires : List (Fin W) := s.left ++ d.outputs v ++ s.right

/-- Read the typed row from the geometric reconstruction, with one box and
the shared through-wires on both sides. -/
def row : Sliced.Row S
    (s.left.map d.label ++ (S.source (d.generator v) ++ s.right.map d.label))
    (s.left.map d.label ++ (S.target (d.generator v) ++ s.right.map d.label)) :=
  Sliced.Row.pass (s.left.map d.label)
    (.box (d.generator v) (Sliced.Row.straight (s.right.map d.label)))

end EventSlice
end Diagram
end Silmaril.RuntimeWires.ProgressiveGraph
