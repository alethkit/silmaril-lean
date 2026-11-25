module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSimultaneous.Slicing
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
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
