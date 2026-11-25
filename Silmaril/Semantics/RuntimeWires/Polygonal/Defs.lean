module

public import Silmaril.Semantics.RuntimeWires.Polygraph.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Fin.Basic

@[expose] public section

/-!
# Layered progressive polygonal diagrams

An independent geometric model for Definition 3.2 and Figure 7 (pp. 9:6–9:7)
of Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5. This model uses horizontal slabs and rectangular
generator boxes. Height increases in the direction of execution.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Polygonal

universe u v

abbrev Point := ℝ × ℝ

/-- A horizontal slab with positive height. -/
structure Slab where
  lower : ℝ
  upper : ℝ
  increasing : lower < upper

def interpolate (x y t : ℝ) : ℝ := (1 - t) * x + t * y

/-- A straight strand across a slab, given by its two horizontal coordinates. -/
structure Strand (slab : Slab) where
  start : ℝ
  finish : ℝ

namespace Strand

variable {slab : Slab}

def point (s : Strand slab) (t : ℝ) : Point :=
  (interpolate s.start s.finish t, interpolate slab.lower slab.upper t)

/-- The closed segment traced by the strand. -/
def trace (s : Strand slab) : Set Point :=
  s.point '' Set.Icc 0 1

end Strand

variable {O : Type u}

/-- An ordered typed frontier with one distinct position for each value in the word. -/
structure Frontier (word : List O) where
  positions : List ℝ
  length_eq : positions.length = word.length
  ordered : positions.Pairwise (· < ·)

namespace Frontier

def empty : Frontier ([] : List O) := ⟨[], rfl, .nil⟩

def singleton (label : O) (x : ℝ) : Frontier [label] :=
  ⟨[x], rfl, .cons (by simp) .nil⟩

def coordinate {A : List O} (p : Frontier A) (i : Fin A.length) : ℝ :=
  p.positions.get (Fin.cast p.length_eq.symm i)

/-- Concatenate two ordered frontiers whose positions are strictly separated. -/
def append {A B : List O} (p : Frontier A) (q : Frontier B)
    (h : ∀ x ∈ p.positions, ∀ y ∈ q.positions, x < y) : Frontier (A ++ B) where
  positions := p.positions ++ q.positions
  length_eq := by simp only [List.length_append, p.length_eq, q.length_eq]
  ordered := List.pairwise_append.mpr ⟨p.ordered, q.ordered, h⟩

end Frontier

/-- Strands joining the corresponding ordered ports of two equally typed boundaries. -/
def connector {A : List O} (slab : Slab) (p q : Frontier A) (i : Fin A.length) : Strand slab :=
  ⟨p.coordinate i, q.coordinate i⟩

/-- A through strand in a horizontal slot. Its endpoints stay strictly inside. -/
structure Through (floor : ℝ) where
  limit : ℝ
  start : ℝ
  finish : ℝ
  start_left : floor < start
  start_right : start < limit
  finish_left : floor < finish
  finish_right : finish < limit

variable {S : Signature.{u,v} O}

/-- A labeled generator box with ports on the two horizontal sides.
The ports may be empty on either side. -/
structure Box (S : Signature.{u,v} O) (floor : ℝ) (e : S.Edge) where
  left : ℝ
  right : ℝ
  left_bound : floor < left
  width : left < right
  input : Frontier (S.source e)
  output : Frontier (S.target e)
  input_inside : ∀ x ∈ input.positions, left < x ∧ x < right
  output_inside : ∀ x ∈ output.positions, left < x ∧ x < right

/-- The rectangle occupied by a generator box in its slab. -/
def Box.trace {floor : ℝ} {e : S.Edge} (box : Box S floor e) (slab : Slab) : Set Point :=
  {p | p.1 ∈ Set.Icc box.left box.right ∧ p.2 ∈ Set.Icc slab.lower slab.upper}

/-- A layer of boxes and through strands. Each subsequent slot lies to the
right of the preceding slot. Horizontal size and strand coordinates are data. -/
inductive Layer (S : Signature.{u,v} O) : ℝ → List O → List O → Type (max u v)
  | empty (floor : ℝ) : Layer S floor [] []
  | wire {floor : ℝ} {A B : List O} (label : O) (wire : Through floor)
      (rest : Layer S wire.limit A B) : Layer S floor (label :: A) (label :: B)
  | box {floor : ℝ} {A B : List O} (e : S.Edge) (box : Box S floor e)
      (rest : Layer S box.right A B) : Layer S floor (S.source e ++ A) (S.target e ++ B)

namespace Layer

/-- The covered sets of the layer's cells, in horizontal order. -/
def traces (slab : Slab) : {floor : ℝ} → {A B : List O} → Layer S floor A B → List (Set Point)
  | _, _, _, .empty _ => []
  | _, _, _, .wire _ w rest => (Strand.mk (slab := slab) w.start w.finish).trace ::
      traces slab rest
  | _, _, _, .box _ b rest => b.trace slab :: traces slab rest

end Layer
end Silmaril.RuntimeWires.Polygonal
