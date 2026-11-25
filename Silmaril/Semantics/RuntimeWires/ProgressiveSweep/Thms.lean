module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
public import Mathlib.Data.Finset.Max
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSweep.Boundary
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSweep.Readback

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}

theorem landmark_strict : StrictMono d.landmark :=
  Proofs.ProgressiveSweep.landmark_strict d

theorem cut_regular (i : Fin (V + 1)) : d.Regular (d.cutHeight i) :=
  Proofs.ProgressiveSweep.cut_regular d i

theorem cut_isolates (i : Fin V) :
    d.Isolates (d.vertexOrder i) (d.cutHeight i.castSucc) (d.cutHeight i.succ) :=
  Proofs.ProgressiveSweep.cut_isolates d i

/-- Read the whole graph by choosing its unique wire lists at the
midpoints of the gaps in its ordered heights. -/
noncomputable def sweep (d : Diagram S V W) : d.Sweep :=
  Proofs.ProgressiveSweep.sweep d

namespace Sweep

theorem wire_span (s : d.Sweep) (i : Fin (V + 1)) (w : Fin W) :
    w ∈ s.wires i ↔ (d.startIndex w).val ≤ i.val ∧ i.val < (d.finishIndex w).val :=
  Proofs.ProgressiveSweep.wire_span s i w

theorem some_cut (s : d.Sweep) (w : Fin W) : ∃ i, w ∈ s.wires i :=
  Proofs.ProgressiveSweep.some_cut s w

theorem wireCuts_nonempty (s : d.Sweep) (w : Fin W) : (s.wireCuts w).Nonempty :=
  Proofs.ProgressiveSweep.wireCuts_nonempty s w

/-- Read the starting vertex from the first cut featuring this wire ID. -/
noncomputable def readStart (s : d.Sweep) (w : Fin W) : Option (Fin V) :=
  d.vertexAt (((s.wireCuts w).min' (s.wireCuts_nonempty w)).castSucc)

/-- Read the finishing vertex from the landmark after this wire's last cut. -/
noncomputable def readFinish (s : d.Sweep) (w : Fin W) : Option (Fin V) :=
  d.vertexAt (((s.wireCuts w).max' (s.wireCuts_nonempty w)).succ)

theorem readStart_eq (s : d.Sweep) (w : Fin W) : s.readStart w = d.start w := by
  rw [readStart, Proofs.ProgressiveSweep.first_index, Proofs.ProgressiveSweep.vertexAt_start]

theorem readFinish_eq (s : d.Sweep) (w : Fin W) : s.readFinish w = d.finish w := by
  rw [readFinish, Proofs.ProgressiveSweep.last_index, Proofs.ProgressiveSweep.vertexAt_finish]

/-- The endpoint rank identifies the incident input at the given event. -/
theorem wire_input (i : Fin V) (w : Fin W) :
    w ∈ d.inputs (d.vertexOrder i) ↔ (d.finishIndex w).val = i.val + 1 :=
  Proofs.ProgressiveSweep.wire_input i w

/-- The endpoint rank identifies the incident output at the given event. -/
theorem wire_output (i : Fin V) (w : Fin W) :
    w ∈ d.outputs (d.vertexOrder i) ↔ (d.startIndex w).val = i.val + 1 :=
  Proofs.ProgressiveSweep.wire_output i w

theorem input_mem (s : d.Sweep) (w : Fin W) : w ∈ s.wires 0 ↔ d.start w = none :=
  Proofs.ProgressiveSweep.input_mem s w

theorem output_mem (s : d.Sweep) (w : Fin W) : w ∈ s.wires (Fin.last V) ↔ d.finish w = none :=
  Proofs.ProgressiveSweep.output_mem s w

theorem input_order (s : d.Sweep) : (s.wires 0).Pairwise (fun a b => d.x a 0 < d.x b 0) :=
  Proofs.ProgressiveSweep.input_order s

theorem output_order (s : d.Sweep) :
    (s.wires (Fin.last V)).Pairwise (fun a b => d.x a 1 < d.x b 1) :=
  Proofs.ProgressiveSweep.output_order s

/-- Read the row at the types of the two global cut lists. -/
@[expose] noncomputable def row (s : d.Sweep) (i : Fin V) :
    Sliced.Row S ((s.wires i.castSucc).map d.label) ((s.wires i.succ).map d.label) :=
  (congrArg₂ (Sliced.Row S)
    (congrArg (List.map d.label) (s.before i)) (congrArg (List.map d.label) (s.after i))).mp
    (s.event i).cutRow

/-- Assemble a finite sequence of rows at its successive typed frontiers. -/
@[expose] def joinRows {n : ℕ} (word : Fin (n + 1) → List O)
    (row : ∀ i : Fin n, Sliced.Row S (word i.castSucc) (word i.succ)) :
    Sliced.Sheet S (word 0) (word (Fin.last n)) :=
  match n with
  | 0 => .empty _
  | _ + 1 => .cons (row 0) (joinRows (word ∘ Fin.succ) (fun i => row i.succ))

/-- Compose one row per vertex into the typed sheet at the cap words. -/
@[expose] noncomputable def sheet (s : d.Sweep) :
    Sliced.Sheet S ((s.wires 0).map d.label) ((s.wires (Fin.last V)).map d.label) :=
  joinRows (fun i => (s.wires i).map d.label) s.row

end Sweep
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
