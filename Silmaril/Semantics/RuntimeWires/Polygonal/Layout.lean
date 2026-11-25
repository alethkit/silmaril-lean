module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Defs
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Order a frontier by its increasing position function. -/
def Frontier.ofCoordinates {A : List O} (x : Fin A.length → ℝ) (h : StrictMono x) : Frontier A :=
  ⟨List.ofFn x, List.length_ofFn, List.pairwise_ofFn.mpr h⟩

/-- A frontier strictly to the right of a horizontal bound. -/
structure BoundedFrontier (floor : ℝ) (A : List O) where
  frontier : Frontier A
  right_of_bound : ∀ x ∈ frontier.positions, floor < x

namespace BoundedFrontier

def empty (floor : ℝ) : BoundedFrontier floor ([] : List O) :=
  ⟨Frontier.empty, by simp [Frontier.empty]⟩

/-- Attach a bounded tail to a block to its left, preserving port order. -/
def prepend {floor limit : ℝ} {A B : List O} (p : Frontier A)
    (q : BoundedFrontier limit B) (gap : floor < limit)
    (lo : ∀ x ∈ p.positions, floor < x) (hi : ∀ x ∈ p.positions, x ≤ limit) :
    BoundedFrontier floor (A ++ B) where
  frontier := p.append q.frontier
    (fun x hx y hy => (hi x hx).trans_lt (q.right_of_bound y hy))
  right_of_bound x hx := by
    change x ∈ p.positions ++ q.frontier.positions at hx
    exact (List.mem_append.mp hx).elim (lo x) (fun h => gap.trans (q.right_of_bound x h))

def prependWire {floor limit : ℝ} {B : List O} (label : O) (x : ℝ)
    (lo : floor < x) (hi : x < limit) (q : BoundedFrontier limit B) :
    BoundedFrontier floor (label :: B) :=
  prepend (Frontier.singleton label x) q (lo.trans hi)
    (fun _ h => List.mem_singleton.mp h ▸ lo)
    (fun _ h => List.mem_singleton.mp h ▸ hi.le)

end BoundedFrontier

namespace Layer

/-- The ordered input ports of the layer, including through-wire endpoints. -/
def inputs : {floor : ℝ} → {A B : List O} → Layer S floor A B → BoundedFrontier floor A
  | floor, _, _, .empty _ => .empty floor
  | _, _, _, .wire a w rest =>
    BoundedFrontier.prependWire a w.start w.start_left w.start_right (inputs rest)
  | _, _, _, .box _ b rest =>
    BoundedFrontier.prepend b.input (inputs rest) (b.left_bound.trans b.width)
      (fun x hx => b.left_bound.trans (b.input_inside x hx).1)
      (fun x hx => (b.input_inside x hx).2.le)

/-- The ordered output ports of the layer, including through-wire endpoints. -/
def outputs : {floor : ℝ} → {A B : List O} → Layer S floor A B → BoundedFrontier floor B
  | floor, _, _, .empty _ => .empty floor
  | _, _, _, .wire a w rest =>
    BoundedFrontier.prependWire a w.finish w.finish_left w.finish_right (outputs rest)
  | _, _, _, .box _ b rest =>
    BoundedFrontier.prepend b.output (outputs rest) (b.left_bound.trans b.width)
      (fun x hx => b.left_bound.trans (b.output_inside x hx).1)
      (fun x hx => (b.output_inside x hx).2.le)

end Layer

/-- A typed polygonal drawing with its input height as an index.
Every layer is followed by a positive connector slab. The connector joins
the layer's ordered output ports to the next layer's ordered input ports.
A terminal slab carries the last word by through strands. -/
inductive Drawing (S : Signature.{u,v} O) : ℝ → List O → List O → Type (max u v)
  | straight {A : List O} (slab : Slab) (ports : Frontier A) : Drawing S slab.lower A A
  | stack {A M B : List O} {floor next : ℝ} (slab : Slab) (layer : Layer S floor A M)
      (gap : slab.upper < next) (rest : Drawing S next M B) : Drawing S slab.lower A B

namespace Drawing

def input {height : ℝ} {A B : List O} : Drawing S height A B → Frontier A
  | .straight _ p => p
  | .stack _ layer _ _ => layer.inputs.frontier

/-- The output height and ordered outer output frontier of a drawing. -/
def output : {height : ℝ} → {A B : List O} → Drawing S height A B → ℝ × Frontier B
  | _, _, _, .straight slab p => (slab.upper, p)
  | _, _, _, .stack _ _ _ rest => output rest

end Drawing

/-- The covered sets belonging to one slab of a drawing. -/
structure Part where
  slab : Slab
  traces : List (Set Point)

namespace Part

def connector {A : List O} (slab : Slab) (p q : Frontier A) : Part :=
  ⟨slab, List.ofFn (fun i => (Polygonal.connector slab p q i).trace)⟩

def Contains (piece : Part) (p : Point) : Prop :=
  ∃ region ∈ piece.traces, p ∈ region

/-- Cells are disjoint within a slab and stay between its two caps. -/
def Valid (piece : Part) : Prop :=
  piece.traces.Pairwise Disjoint ∧
    ∀ p, piece.Contains p → p.2 ∈ Set.Icc piece.slab.lower piece.slab.upper

end Part

/-- The drawing as a sequence of slabs with their actual planar traces. -/
def Drawing.parts : {height : ℝ} → {A B : List O} → Drawing S height A B → List Part
  | _, _, _, .straight slab p => [Part.connector slab p p]
  | _, _, _, .stack slab layer gap rest =>
    ⟨slab, layer.traces slab⟩ ::
      Part.connector ⟨slab.upper, _, gap⟩ layer.outputs.frontier rest.input :: parts rest

end Silmaril.RuntimeWires.Polygonal
