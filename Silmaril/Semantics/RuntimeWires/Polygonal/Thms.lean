module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Realization
import Silmaril.Proofs.Semantics.RuntimeWires.Polygonal.Drawing
import Silmaril.Proofs.Semantics.RuntimeWires.Polygonal.Realization

@[expose] public section

/-!
The bridge realizes every typed sheet in the restricted polygonal model.
The horizontal sections of a connector at any interior level recover
the same ordered typed word. This local cut statement uses the same fixed
polygonal drawing. Slicing arbitrary progressive embeddings, comparing
different layerings of a drawing, and relating the model to general
boundary-relative planar isotopy remain separate.
-/

namespace Silmaril.RuntimeWires.Polygonal

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A B : List O}

/-- Each strand has strictly increasing height along its segment. -/
theorem Strand.strictHeight {slab : Slab} (s : Strand slab) :
    StrictMono (fun t => (s.point t).2) :=
  Proofs.Polygonal.height_strict s

/-- Distinct strands in a connector never intersect. -/
theorem connector_trace_disjoint (slab : Slab) (p q : Frontier A)
    {i j : Fin A.length} (h : i ≠ j) :
    Disjoint (connector slab p q i).trace (connector slab p q j).trace :=
  Proofs.Polygonal.connector_disjoint slab p q h

/-- A horizontal cut through a connector meets each strand at exactly one
point, in the same order and with the same port labels. -/
theorem connector_ordered_cut (slab : Slab) (p q : Frontier A)
    {height : ℝ} (h : height ∈ Set.Icc slab.lower slab.upper) :
    ∃ cut : Frontier A, ∀ i : Fin A.length,
      (connector slab p q i).trace ∩ {z : Point | z.2 = height} = {(cut.coordinate i, height)} :=
  Proofs.Polygonal.connector_cut slab p q h

/-- Different cells in the same layer have disjoint planar traces. -/
theorem Layer.disjoint_traces (slab : Slab) {floor : ℝ} (r : Layer S floor A B) :
    (r.traces slab).Pairwise Disjoint :=
  Proofs.Polygonal.layer_disjoint slab r

/-- A layer's declared input port lies on its covered geometry. -/
theorem Layer.input_traced (slab : Slab) {floor x : ℝ} (r : Layer S floor A B)
    (h : x ∈ r.inputs.frontier.positions) :
    ∃ region ∈ r.traces slab, (x, slab.lower) ∈ region :=
  Proofs.Polygonal.input_covered r h

/-- A layer's declared output port lies on its covered geometry. -/
theorem Layer.output_traced (slab : Slab) {floor x : ℝ} (r : Layer S floor A B)
    (h : x ∈ r.outputs.frontier.positions) :
    ∃ region ∈ r.traces slab, (x, slab.upper) ∈ region :=
  Proofs.Polygonal.output_covered r h

/-- Every part contains disjoint cells confined to its specified slab. -/
theorem Drawing.valid_parts {height : ℝ} (d : Drawing S height A B)
    {piece : Part} (h : piece ∈ d.parts) : piece.Valid :=
  Proofs.Polygonal.drawing_valid d h

/-- The parts of the drawing have disjoint vertical interiors, in execution order. -/
theorem Drawing.ordered_parts {height : ℝ} (d : Drawing S height A B) :
    d.parts.Pairwise (fun earlier later => earlier.slab.upper ≤ later.slab.lower) :=
  Proofs.Polygonal.drawing_order d

/-- Traces in vertically ordered parts can meet only at a common cap. -/
theorem Part.contact_at_cap {earlier later : Part} (he : earlier.Valid) (hl : later.Valid)
    (order : earlier.slab.upper ≤ later.slab.lower) {p : Point}
    (hp : earlier.Contains p) (hq : later.Contains p) :
    p.2 = earlier.slab.upper ∧ p.2 = later.slab.lower :=
  Proofs.Polygonal.shared_cap he hl order hp hq

/-- A connector meets the preceding part only at its declared starting port. -/
theorem connector_contact_at_start {previous : Part} {slab : Slab} (h : previous.Valid)
    (order : previous.slab.upper ≤ slab.lower) (p q : Frontier A) (i : Fin A.length)
    {z : Point} (hp : previous.Contains z) (hc : z ∈ (connector slab p q i).trace) :
    z = (p.coordinate i, slab.lower) :=
  Proofs.Polygonal.connector_entry h order p q i hp hc

/-- A connector meets the following part only at its declared finishing port. -/
theorem connector_contact_at_finish {slab : Slab} {following : Part} (h : following.Valid)
    (order : slab.upper ≤ following.slab.lower) (p q : Frontier A) (i : Fin A.length)
    {z : Point} (hp : following.Contains z) (hc : z ∈ (connector slab p q i).trace) :
    z = (q.coordinate i, slab.upper) :=
  Proofs.Polygonal.connector_exit h order p q i hp hc

/-- The ordered layers of the geometric realization reconstruct the original
sheet, with its full typed row sequence. -/
theorem Drawing.read_realize (height : ℝ) (p : Sheet S A B) :
    (Drawing.realize height p).readSheet = p :=
  Proofs.Polygonal.read_realized_sheet height p

end Silmaril.RuntimeWires.Polygonal
