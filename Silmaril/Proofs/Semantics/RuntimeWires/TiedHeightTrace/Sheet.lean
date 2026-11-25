module

public import Silmaril.Proofs.Semantics.RuntimeWires.TiedHeightTrace.Names
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.TiedHeightTrace

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable (s : d.LayerSweep)

private theorem trace_reindex {A B C D : List O} (hA : A = C) (hB : B = D) (r : Row S A B)
    (row box : ℕ) (input : List (NamedWire O)) :
    (r.reindex hA hB).traceWires row box input = r.traceWires row box input := by
  subst C
  subst D
  rfl

/-- The decoder preserves through names and reads each box's ordered ports.
The initial ordinal counts the boxes preceding this suffix, even when
their input and output words are both empty. -/
private theorem trace_layerRow (slots : List (Diagram.LayerSlot V W)) (row box : ℕ)
    (nd : (slots.filterMap Sum.getRight?).Nodup)
    (outputNames : ∀ v ∈ slots.filterMap Sum.getRight?,
      namePorts (.box row (box + (slots.filterMap Sum.getRight?).idxOf v))
        (S.target (d.generator v)) = (d.outputs v).map s.namedWire) :
    (d.layerRow slots).traceWires row box ((slots.flatMap d.slotInputs).map s.namedWire) =
      ⟨(slots.flatMap d.slotOutputs).map s.namedWire,
        (slots.filterMap Sum.getRight?).map s.expectedBox⟩ := by
  induction slots generalizing box with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inl w =>
      have tail := ih box nd outputNames
      change (.wire (d.label w) (d.layerRow slots) : Row S _ _).traceWires row box
        (s.namedWire w :: (slots.flatMap d.slotInputs).map s.namedWire) =
        ⟨s.namedWire w :: (slots.flatMap d.slotOutputs).map s.namedWire,
          (slots.filterMap Sum.getRight?).map s.expectedBox⟩
      simp [Row.traceWires, tail]
    | inr v =>
      let vertices := slots.filterMap Sum.getRight?
      change (v :: vertices).Nodup at nd
      change ∀ j ∈ v :: vertices,
        namePorts (.box row (box + (v :: vertices).idxOf j)) (S.target (d.generator j)) =
          (d.outputs j).map s.namedWire at outputNames
      have head : namePorts (.box row box) (S.target (d.generator v)) =
          (d.outputs v).map s.namedWire := by
        simpa only [List.idxOf_cons_self, Nat.add_zero] using outputNames v List.mem_cons_self
      have tail := ih (box + 1) (List.nodup_cons.mp nd).2 (by
        intro j hj
        have different : v ≠ j := fun eq => (List.nodup_cons.mp nd).1 (eq.symm ▸ hj)
        have h := outputNames j (List.mem_cons_of_mem _ hj)
        have shift : box + (vertices.idxOf j).succ = box + 1 + vertices.idxOf j := by omega
        rw [List.idxOf_cons_ne _ different, shift] at h
        exact h)
      have count : ((d.inputs v).map s.namedWire).length = (S.source (d.generator v)).length := by
        simp [Diagram.inputs]
      change (.box (d.generator v) (d.layerRow slots) : Row S _ _).traceWires row box
        ((d.inputs v ++ slots.flatMap d.slotInputs).map s.namedWire) =
        ⟨(d.outputs v ++ slots.flatMap d.slotOutputs).map s.namedWire,
          s.expectedBox v :: (slots.filterMap Sum.getRight?).map s.expectedBox⟩
      simp only [List.map_append, Row.traceWires, List.take_left' count, List.drop_left' count, head, tail]
      rfl

theorem row_trace (i : Fin d.levelCount) :
    (s.row i).traceWires i.val 0 ((s.wires i.castSucc).map s.namedWire) =
      ⟨(s.wires i.succ).map s.namedWire, (s.layer i).vertices.map s.expectedBox⟩ := by
  have nd : (s.layer i).vertices.Nodup :=
    (s.layer i).vertices_order.imp (fun h => ne_of_apply_ne d.vertexX (ne_of_lt h))
  have h := trace_layerRow s (s.layer i).slots i.val 0 nd (by
    intro v hv
    simpa only [Nat.zero_add, Diagram.LayerSlice.vertices] using box_output_names s i v hv)
  have transport : (s.row i).traceWires i.val 0 ((s.wires i.castSucc).map s.namedWire) =
      (s.layer i).row.traceWires i.val 0 ((s.wires i.castSucc).map s.namedWire) :=
    (trace_reindex (congrArg (List.map d.label) (s.before i))
      (congrArg (List.map d.label) (s.after i)) (s.layer i).cutRow _ _ _).trans
      (trace_reindex (s.layer i).input_types.symm (s.layer i).output_types.symm (s.layer i).row _ _ _)
  rw [transport, ← s.before i, ← s.after i]
  exact h

theorem sheet_trace : s.sheet.traceWires = s.expectedTrace := by
  rw [Sheet.traceWires, boundary_names s, Diagram.LayerSweep.sheet, Diagram.LayerSweep.expectedTrace]
  exact Sheet.traceWiresFrom_joinRows s.word s.row (fun i => (s.wires i).map s.namedWire)
    (fun i => (s.layer i).vertices.map s.expectedBox) 0
    (fun i => by simpa only [Nat.zero_add] using row_trace s i)

end Silmaril.RuntimeWires.Proofs.TiedHeightTrace
