module

public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.TiedHeightSweep.Sweep

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}

theorem levelHeight_index (v : Fin V) : d.levelHeight (d.levelIndex v) = d.vertexHeight v :=
  Proofs.TiedHeightSweep.levelHeight_index d v

theorem vertex_at_level (i : Fin d.levelCount) : ∃ v, d.vertexHeight v = d.levelHeight i :=
  Proofs.TiedHeightSweep.vertex_at_level d i

theorem level_strict : StrictMono d.levelHeight :=
  Proofs.TiedHeightSweep.level_strict d

theorem level_landmarks_strict : StrictMono d.levelLandmark :=
  Proofs.TiedHeightSweep.landmarks_strict d

theorem level_gap_regular {i : Fin (d.levelCount + 1)} {h : ℝ} (hh : h ∈ d.levelGap i) :
    d.Regular h :=
  Proofs.TiedHeightSweep.gap_regular d hh

theorem level_gap_isolates (i : Fin d.levelCount) {lo hi : ℝ}
    (hl : lo ∈ d.levelGap i.castSucc) (hr : hi ∈ d.levelGap i.succ) :
    d.IsolatesLayer (d.levelHeight i) lo hi :=
  Proofs.TiedHeightSweep.gap_isolates d i hl hr

/-- There is a regular cut in every gap, including the single gap when
the diagram has no vertices. -/
noncomputable def layerMidpoints (d : Diagram S V W .point) : d.LayerCuts :=
  Proofs.TiedHeightSweep.midpointCuts d

/-- Construct the entire sequence of isolated layers at chosen regular cuts. -/
noncomputable def layerSweepAt (d : Diagram S V W .point) (cuts : d.LayerCuts) : d.LayerSweep :=
  Proofs.TiedHeightSweep.sweepAt d cuts

@[simp] theorem layerSweepAt_cuts (d : Diagram S V W .point) (cuts : d.LayerCuts) :
    (d.layerSweepAt cuts).cuts = cuts :=
  Proofs.TiedHeightSweep.sweepAt_cuts d cuts

noncomputable def layerSweep (d : Diagram S V W .point) : d.LayerSweep :=
  d.layerSweepAt d.layerMidpoints

namespace LayerSweep

variable (s : d.LayerSweep)

/-- Each wire appears on exactly the contiguous range of cuts between its
endpoint landmarks. The ordered slot decomposition records its ports at the endpoints. -/
theorem wire_span (i : Fin (d.levelCount + 1)) (w : Fin W) :
    w ∈ s.wires i ↔ (d.layerStartIndex w).val ≤ i.val ∧ i.val < (d.layerFinishIndex w).val :=
  Proofs.TiedHeightSweep.wire_span s i w

theorem some_cut (w : Fin W) : ∃ i, w ∈ s.wires i :=
  Proofs.TiedHeightSweep.some_cut s w

theorem vertex_mem (i : Fin d.levelCount) (v : Fin V) :
    v ∈ (s.layer i).vertices ↔ d.levelIndex v = i := by
  rw [(s.layer i).vertices_exact, ← levelHeight_index v]
  exact ⟨fun eq => (level_strict (d := d)).injective eq, congrArg d.levelHeight⟩

theorem input_mem (w : Fin W) : w ∈ s.wires 0 ↔ d.start w = none :=
  Proofs.TiedHeightSweep.input_mem s w

theorem output_mem (w : Fin W) : w ∈ s.wires (Fin.last d.levelCount) ↔ d.finish w = none :=
  Proofs.TiedHeightSweep.output_mem s w

theorem input_order : (s.wires 0).Pairwise (fun a b => d.x a 0 < d.x b 0) :=
  Proofs.TiedHeightSweep.input_order s

theorem output_order : (s.wires (Fin.last d.levelCount)).Pairwise (fun a b => d.x a 1 < d.x b 1) :=
  Proofs.TiedHeightSweep.output_order s

/-- The ordered wire-ID list at every gap is independent of the cut height. -/
theorem wires_eq (t : d.LayerSweep) (i : Fin (d.levelCount + 1)) : s.wires i = t.wires i :=
  Proofs.TiedHeightSweep.wires_eq s t i

/-- The geometric sheets agree after transporting their cap words along
the ordered wire-list equalities. -/
theorem sheet_eq (t : d.LayerSweep) :
    (congrArg₂ (Sheet S) (congrArg (List.map d.label) (s.wires_eq t 0))
      (congrArg (List.map d.label) (s.wires_eq t (Fin.last d.levelCount)))).mp s.sheet = t.sheet :=
  Proofs.TiedHeightSweep.sheet_eq s t

/-- Independently serializing each layer preserves the seam class of the
whole sheet at its actual cap words. -/
theorem serial_seam (p : s.Schedule) : Sheet.SeamEquivalent (s.serialSheet p) s.sheet :=
  Proofs.TiedHeightSweep.serial_seam s p

theorem serial_equiv (p q : s.Schedule) :
    Sheet.SeamEquivalent (s.serialSheet p) (s.serialSheet q) :=
  .trans _ _ _ (s.serial_seam p) (.symm _ _ (s.serial_seam q))

end LayerSweep
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
