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

theorem cap_landmarks_strict {n : ℕ} {height : Fin n → ℝ}
    (inside : ∀ i, height i ∈ Set.Ioo 0 1) (ordered : StrictMono height) :
    StrictMono (Fin.cons 0 (Fin.snoc height 1)) :=
  Proofs.ProgressiveSweep.cap_landmarks_strict inside ordered

theorem OrderedCut.input_boundary_order {kind : VertexSeparation} {d : Diagram S V W kind}
    {h : ℝ} {wires : List (Fin W)} (cut : d.OrderedCut h wires)
    (hh : 0 < h) (incident : ∀ w ∈ wires, d.start w = none) :
    wires.Pairwise (fun a b => d.x a 0 < d.x b 0) :=
  Proofs.ProgressiveSweep.input_boundary_order cut hh incident

theorem OrderedCut.output_boundary_order {kind : VertexSeparation} {d : Diagram S V W kind}
    {h : ℝ} {wires : List (Fin W)} (cut : d.OrderedCut h wires)
    (hh : h < 1) (incident : ∀ w ∈ wires, d.finish w = none) :
    wires.Pairwise (fun a b => d.x a 1 < d.x b 1) :=
  Proofs.ProgressiveSweep.output_boundary_order cut hh incident

theorem landmark_strict : StrictMono d.landmark :=
  Proofs.ProgressiveSweep.landmark_strict d

theorem gap_regular {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i) : d.Regular h :=
  Proofs.ProgressiveSweep.gap_regular d hh

theorem gap_isolates (i : Fin V) {lo hi : ℝ} (hl : lo ∈ d.gap i.castSucc) (hr : hi ∈ d.gap i.succ) :
    d.Isolates (d.vertexOrder i) lo hi :=
  Proofs.ProgressiveSweep.gap_isolates d i hl hr

theorem gap_crosses_iff_indices {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i) (w : Fin W) :
    d.crosses w h ↔ (d.startIndex w).val ≤ i.val ∧ i.val < (d.finishIndex w).val :=
  Proofs.ProgressiveSweep.gap_crosses_iff_indices d hh w

theorem cut_regular (i : Fin (V + 1)) : d.Regular (d.cutHeight i) :=
  d.gap_regular (Proofs.ProgressiveSweep.midpoint_in_gap d i)

theorem cut_isolates (i : Fin V) :
    d.Isolates (d.vertexOrder i) (d.cutHeight i.castSucc) (d.cutHeight i.succ) :=
  d.gap_isolates i (Proofs.ProgressiveSweep.midpoint_in_gap d _) (Proofs.ProgressiveSweep.midpoint_in_gap d _)

/-- Read a sheet at the chosen regular heights. -/
noncomputable def sweepAt (d : Diagram S V W) (cuts : d.Cuts) : d.Sweep :=
  Proofs.ProgressiveSweep.sweepAt d cuts

@[simp] theorem sweepAt_cuts (d : Diagram S V W) (cuts : d.Cuts) :
    (d.sweepAt cuts).cuts = cuts :=
  Proofs.ProgressiveSweep.sweepAt_cuts d cuts

/-- The midpoint sweep is a particular choice of a regular cut in each gap. -/
noncomputable def sweep (d : Diagram S V W) : d.Sweep :=
  d.sweepAt ⟨d.cutHeight, Proofs.ProgressiveSweep.midpoint_in_gap d⟩

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
