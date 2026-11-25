module

public import Silmaril.Semantics.RuntimeWires.LayerSerialization.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.LayerSerialization.Splits
import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable {d : Diagram S V W kind}

/-- Splitting at an intermediate set of completed slots retains the same
position for each vertex box and each through block. -/
theorem layerStep_split {a b c : Finset (Fin V)} (hab : a ⊆ b) (hbc : b ⊆ c)
    (slots : List (LayerSlot V W)) :
    Row.Split S (d.layerStep (hab.trans hbc) slots) (d.layerStep hab slots)
      (d.layerStep hbc slots) :=
  Proofs.LayerSerialization.layerStep_split d hab hbc slots

theorem frontier_empty (slots : List (LayerSlot V W)) :
    d.frontier ∅ slots = slots.flatMap d.slotSource :=
  Proofs.LayerSerialization.frontier_empty d slots

theorem frontier_full (slots : List (LayerSlot V W)) (done : Finset (Fin V))
    (covers : ∀ j, Sum.inr j ∈ slots → j ∈ done) :
    d.frontier done slots = slots.flatMap d.slotTarget :=
  Proofs.LayerSerialization.frontier_full d slots done covers

namespace LayerSlice

variable {height lo hi : ℝ} (s : d.LayerSlice height lo hi)

theorem covers_of_perm {order : List (Fin V)} (perm : order.Perm s.vertices) :
    ∀ j, Sum.inr j ∈ s.slots → j ∈ completed ∅ order := by
  intro j hj
  exact (Proofs.LayerSerialization.mem_completed ∅ order j).mpr
    (Or.inr (perm.mem_iff.mpr (List.mem_filterMap.mpr ⟨.inr j, hj, rfl⟩)))

/-- Execute the layer's vertex slots in any prescribed permutation. The
outer boundary words are those of the original layer row. -/
def serialize (order : List (Fin V)) (perm : order.Perm s.vertices) :
    Sheet S (s.slots.flatMap d.slotSource) (s.slots.flatMap d.slotTarget) :=
  (d.serializeFrom s.slots ∅ order).reindex
    (frontier_empty s.slots) (frontier_full s.slots (completed ∅ order) (s.covers_of_perm perm))

/-- Every serialization gives the same seam class as the single layer row. -/
theorem serialize_seam (order : List (Fin V)) (perm : order.Perm s.vertices) :
    Sheet.SeamEquivalent (s.serialize order perm) (.cons s.row (.empty _)) :=
  Proofs.LayerSerialization.serializeFrom_full d s.slots order (s.covers_of_perm perm)

/-- The serial sheet reindexed by the wire labels at the two actual cuts. -/
def serializeCuts {d : Diagram S V W .point} (s : d.LayerSlice height lo hi)
    (order : List (Fin V)) (perm : order.Perm s.vertices) :
    Sheet S ((s.slots.flatMap d.slotInputs).map d.label) ((s.slots.flatMap d.slotOutputs).map d.label) :=
  (s.serialize order perm).reindex s.input_types.symm s.output_types.symm

theorem serializeCuts_seam {d : Diagram S V W .point} (s : d.LayerSlice height lo hi)
    (order : List (Fin V)) (perm : order.Perm s.vertices) :
    Sheet.SeamEquivalent (s.serializeCuts order perm) (.cons s.cutRow (.empty _)) := by
  have h := (s.serialize_seam order perm).reindex s.input_types.symm s.output_types.symm
  simpa only [serializeCuts, Proofs.LayerSerialization.one_row_reindex, cutRow] using h

end LayerSlice
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
