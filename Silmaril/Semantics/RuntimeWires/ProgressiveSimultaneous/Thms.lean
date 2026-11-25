module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSimultaneous.Slicing
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSimultaneous.Layer
import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable {d : Diagram S V W kind} {v z : Fin V} {lo hi : ℝ}

/-- Two distinct vertices on one horizontal line have a strict horizontal order. -/
theorem same_height_order {d : Diagram S V W .point} (different : v ≠ z)
    (height : d.vertexHeight v = d.vertexHeight z) :
    d.vertexX v < d.vertexX z ∨ d.vertexX z < d.vertexX v :=
  lt_or_gt_of_ne (fun hx => different (d.vertex_separation (Prod.ext hx height)))

/-- The incident wire sets of the two ordered vertices are disjoint, including
across an input of one and an output of the other. -/
theorem IsolatesPair.incident_disjoint (pair : d.IsolatesPair v z lo hi) :
    List.Disjoint (d.inputs v ++ d.outputs v) (d.inputs z ++ d.outputs z) :=
  Proofs.ProgressiveSimultaneous.incident_disjoint pair

/-- The two geometric cuts have the same left, middle, and right passing
blocks. The incident blocks occupy the slots determined by the two points. -/
theorem simultaneous_event (pair : d.IsolatesPair v z lo hi) :
    Nonempty (d.PairSlice v z lo hi) :=
  Proofs.ProgressiveSimultaneous.simultaneous_event pair

namespace PairSlice

variable (s : d.PairSlice v z lo hi)

theorem input_types : s.inputWires.map d.label = s.sourceWord := by
  simp [inputWires, sourceWord, Diagram.inputs, d.input_types]

theorem output_types : s.outputWires.map d.label = s.targetWord := by
  simp [outputWires, targetWord, Diagram.outputs, d.output_types]

/-- Both serializations split the same row in distinct geometric slots,
even when the incident word of one of the slots is empty. -/
theorem serialization_eq : Sheet.SeamEquivalent s.leftFirst s.rightFirst :=
  Sheet.swap_rows s.leftRow s.rightRow (.empty _)

end PairSlice

/-- Sort the passing wires and all vertices at the isolated level by their
horizontal coordinates. The input and output decompositions follow this same
slot list, with empty blocks at zero-port vertices. -/
theorem layer_slice {d : Diagram S V W .point} {height lo hi : ℝ}
    (iso : d.IsolatesLayer height lo hi) : Nonempty (d.LayerSlice height lo hi) :=
  Proofs.ProgressiveSimultaneous.layer_slice iso

namespace LayerSlice

variable {d : Diagram S V W .point} {height lo hi : ℝ} (s : d.LayerSlice height lo hi)

theorem vertices_exact (j : Fin V) : j ∈ s.vertices ↔ d.vertexHeight j = height :=
  Proofs.ProgressiveSimultaneous.vertices_exact s j

theorem vertices_order : s.vertices.Pairwise (fun i j => d.vertexX i < d.vertexX j) :=
  Proofs.ProgressiveSimultaneous.vertices_order s

/-- Any two different vertex slots have disjoint incident wire IDs. -/
theorem incident_disjoint {i j : Fin V} (hi : i ∈ s.vertices) (hj : j ∈ s.vertices) (h : i ≠ j) :
    List.Disjoint (d.inputs i ++ d.outputs i) (d.inputs j ++ d.outputs j) :=
  Proofs.ProgressiveSimultaneous.same_level_incident_disjoint h
    (((s.vertices_exact j).mp hj).trans ((s.vertices_exact i).mp hi).symm)

theorem input_types :
    (s.slots.flatMap d.slotInputs).map d.label = s.slots.flatMap d.slotSource :=
  Proofs.ProgressiveSimultaneous.layer_input_types s

theorem output_types :
    (s.slots.flatMap d.slotOutputs).map d.label = s.slots.flatMap d.slotTarget :=
  Proofs.ProgressiveSimultaneous.layer_output_types s

/-- The single layer row typed at the ordered wire labels of the actual cuts. -/
@[expose] def cutRow :
    Row S ((s.slots.flatMap d.slotInputs).map d.label) ((s.slots.flatMap d.slotOutputs).map d.label) :=
  s.row.reindex s.input_types.symm s.output_types.symm

end LayerSlice

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
