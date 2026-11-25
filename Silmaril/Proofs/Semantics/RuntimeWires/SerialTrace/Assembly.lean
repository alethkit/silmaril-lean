module

public import Silmaril.Proofs.Semantics.RuntimeWires.SerialTrace.Schedule
public import Silmaril.Proofs.Semantics.RuntimeWires.SerialTrace.Serialization

public section

namespace Silmaril.RuntimeWires.Proofs.SerialTrace

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private theorem trace_thenDo {A B C : List O} (p : Sheet S A B) (q : Sheet S B C)
    (offset : ℕ) (input : List (NamedWire O)) :
    (p.thenDo q).traceWiresFrom offset input =
      let a := p.traceWiresFrom offset input
      let b := q.traceWiresFrom (offset + a.rows.length) a.outputs
      ⟨a.rows ++ b.rows, b.outputs⟩ := by
  induction p generalizing offset input with
  | empty => simp [Sheet.thenDo, Sheet.traceWiresFrom]
  | cons r p ih =>
    simp only [Sheet.thenDo, Sheet.traceWiresFrom, ih, List.length_cons, List.cons_append,
      Nat.add_assoc, Nat.add_comm 1]

/-- Named frontiers compose even when one segment contributes many rows. -/
private theorem trace_joinSegments {n : ℕ} {I : Type*}
    (word : Fin (n + 1) → List O)
    (segments : ∀ i : Fin n, Sheet S (word i.castSucc) (word i.succ))
    (frontier : Fin (n + 1) → List (NamedWire O))
    (orders : Fin n → List I) (atBox : I → List (BoxTrace S)) (offset : ℕ)
    (step : ∀ i, (segments i).traceWiresFrom (offset + rowsBefore orders i.val) (frontier i.castSucc) =
      ⟨(orders i).map atBox, frontier i.succ⟩) :
    (Sheet.joinSegments word segments).traceWiresFrom offset (frontier 0) =
      ⟨(List.ofFn orders).flatten.map atBox, frontier (Fin.last n)⟩ := by
  induction n generalizing offset with
  | zero => simp [Sheet.joinSegments, Sheet.traceWiresFrom]
  | succ n ih =>
    have head : (segments 0).traceWiresFrom offset (frontier 0) =
        ⟨(orders 0).map atBox, frontier (Fin.succ 0)⟩ := by
      simpa only [Fin.val_zero, rowsBefore_zero, Nat.add_zero, Fin.castSucc_zero] using step 0
    have tail := ih (word ∘ Fin.succ) (fun i => segments i.succ) (frontier ∘ Fin.succ)
      (orders ∘ Fin.succ) (offset + (orders 0).length) (fun i => by
        simpa only [Fin.val_succ, rowsBefore_succ, ← Nat.add_assoc, Function.comp_apply,
          ← Fin.castSucc_succ] using step i.succ)
    have joined := trace_thenDo (segments 0) (Sheet.joinSegments (word ∘ Fin.succ)
      (fun i => segments i.succ)) offset (frontier 0)
    rw [head] at joined
    simp only [List.length_map] at joined
    simp only [Function.comp_apply] at tail
    rw [tail] at joined
    change ((segments 0).thenDo (Sheet.joinSegments (word ∘ Fin.succ)
      (fun i => segments i.succ))).traceWiresFrom offset (frontier 0) = _
    simpa only [List.ofFn_succ, List.flatten_cons, List.map_append, Fin.succ_last,
      Function.comp_def] using joined

variable {V W : ℕ} {d : ProgressiveGraph.Diagram S V W .point}
variable {s : d.LayerSweep} (p : s.Schedule)

theorem segment_trace (i : Fin d.levelCount) :
    (s.serialSegment p i).traceWiresFrom (rowsBefore p.order i.val)
        ((s.wires i.castSucc).map p.namedWire) =
      ⟨(p.order i).map (fun j => [p.expectedBox j]), (s.wires i.succ).map p.namedWire⟩ := by
  let layer := s.layer i
  have slotNd := layer.ordered.imp (fun h => ne_of_apply_ne (d.slotX (d.levelHeight i)) (ne_of_lt h))
  have core := trace_serializeFrom d p.namedWire layer.slots slotNd ∅ (p.order i) (order_nodup p i)
    (rowsBefore p.order i.val) (fun _ h => mem_slot p h) (by simp) (output_names p i)
  have reindex : (s.serialSegment p i).traceWiresFrom (rowsBefore p.order i.val)
      ((s.wires i.castSucc).map p.namedWire) =
      (d.serializeFrom layer.slots ∅ (p.order i)).traceWiresFrom (rowsBefore p.order i.val)
        ((s.wires i.castSucc).map p.namedWire) := by
    simp only [Diagram.LayerSweep.serialSegment, Diagram.LayerSweep.word, Diagram.LayerSlice.serializeCuts,
      Diagram.LayerSlice.serialize, trace_reindex, layer]
  rw [reindex, ← s.before i, ← s.after i]
  rw [frontierWires_empty d, frontierWires_full d layer.slots _ (layer.covers_of_perm (p.perm i))] at core
  exact core

theorem trace_sheet : (s.serialSheet p).traceWires = p.expectedTrace := by
  rw [Sheet.traceWires, boundary_names p, Diagram.LayerSweep.serialSheet,
    Diagram.LayerSweep.Schedule.expectedTrace, Diagram.LayerSweep.Schedule.vertices]
  exact trace_joinSegments s.word (s.serialSegment p) (fun i => (s.wires i).map p.namedWire)
    p.order (fun j => [p.expectedBox j]) 0 (fun i => by simpa only [Nat.zero_add] using segment_trace p i)

end Silmaril.RuntimeWires.Proofs.SerialTrace
