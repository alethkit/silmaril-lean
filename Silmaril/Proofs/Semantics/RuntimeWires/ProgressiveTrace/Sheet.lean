module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveTrace.Names

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveTrace

open Silmaril.RuntimeWires.Sliced Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}

/-- The trace of a row assembly follows any invariant that supplies the
named frontier before and after each row. -/
theorem trace_joinRows {n : ℕ} (word : Fin (n + 1) → List O)
    (row : ∀ i : Fin n, Row S (word i.castSucc) (word i.succ))
    (frontier : Fin (n + 1) → List (NamedWire O))
    (boxes : Fin n → List (BoxTrace S)) (offset : ℕ)
    (step : ∀ i, (row i).traceWires (offset + i.val) 0 (frontier i.castSucc) =
      ⟨frontier i.succ, boxes i⟩) :
    (Diagram.Sweep.joinRows word row).traceWiresFrom offset (frontier 0) =
      ⟨List.ofFn boxes, frontier (Fin.last n)⟩ := by
  induction n generalizing offset with
  | zero => simp [Diagram.Sweep.joinRows, Sheet.traceWiresFrom]
  | succ n ih =>
    have head : (row 0).traceWires offset 0 (frontier 0) = ⟨frontier (Fin.succ 0), boxes 0⟩ := by
      simpa only [Fin.val_zero, Nat.add_zero, Fin.castSucc_zero] using step 0
    have tail (i : Fin n) :
        (row i.succ).traceWires (offset + 1 + i.val) 0 (frontier (i.castSucc.succ)) =
          ⟨frontier (i.succ.succ), boxes i.succ⟩ := by
      have h := step i.succ
      have rank : offset + 1 + i.val = offset + (i.succ).val := by
        simp only [Fin.val_succ]
        omega
      rw [rank]
      exact h
    have next := ih (word ∘ Fin.succ) (fun i => row i.succ)
      (frontier ∘ Fin.succ) (boxes ∘ Fin.succ) (offset + 1) tail
    simp only [Diagram.Sweep.joinRows, Sheet.traceWiresFrom]
    erw [head]
    change (Diagram.Sweep.joinRows (word ∘ Fin.succ) (fun i => row i.succ)).traceWiresFrom
      (offset + 1) (frontier (Fin.succ 0)) =
        ⟨List.ofFn (fun i => boxes i.succ), frontier (Fin.last (n + 1))⟩ at next
    erw [next]
    simp [List.ofFn_succ]

variable (s : d.Sweep)

/-- The row consumes the original incident inputs, preserves the passing
names, and emits the original incident outputs in order. -/
theorem row_trace (i : Fin V) :
    (s.row i).traceWires i.val 0 ((s.wires i.castSucc).map s.namedWire) =
      ⟨(s.wires i.succ).map s.namedWire, [s.expectedBox i]⟩ := by
  rw [Diagram.Sweep.row, trace_transport (congrArg (List.map d.label) (s.before i))
      (congrArg (List.map d.label) (s.after i)),
    Diagram.EventSlice.cutRow, trace_transport_symm (s.event i).before_word (s.event i).after_word,
    ← s.before i, ← s.after i]
  simp only [Diagram.EventSlice.row, Diagram.EventSlice.beforeWires, Diagram.EventSlice.afterWires,
    List.map_append, List.append_assoc]
  rw [trace_one_box]
  · rw [box_output_names s]
    rfl
  · simp
  · simp [Diagram.inputs]
  · simp

theorem sheet_trace :
    s.sheet.traceWires = s.expectedTrace := by
  rw [Sheet.traceWires, boundary_names s, Diagram.Sweep.sheet, Diagram.Sweep.expectedTrace]
  exact trace_joinRows (fun i => (s.wires i).map d.label) s.row
    (fun i => (s.wires i).map s.namedWire) (fun i => [s.expectedBox i]) 0
    (fun i => by simpa only [Nat.zero_add] using row_trace s i)

end Silmaril.RuntimeWires.Proofs.ProgressiveTrace
