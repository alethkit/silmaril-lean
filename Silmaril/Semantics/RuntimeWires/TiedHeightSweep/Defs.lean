module

public import Silmaril.Semantics.RuntimeWires.LayerSerialization.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Thms
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Finite sweep of progressive point vertices with tied heights

This develops the reverse slicing construction for Definition 3.2 (p. 9:6)
and Figure 7 (p. 9:7) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} (d : Diagram S V W .point)

/-- The distinct vertex heights, sorted bottom to top. -/
noncomputable def levels : List ℝ :=
  (Finset.univ.image d.vertexHeight).sort

noncomputable def levelCount : ℕ := d.levels.length

noncomputable def levelHeight (i : Fin d.levelCount) : ℝ := d.levels.get i

theorem vertexHeight_mem_levels (v : Fin V) : d.vertexHeight v ∈ d.levels := by
  simp [levels]

/-- Vertices at the same height have the same level index. -/
noncomputable def levelIndex (v : Fin V) : Fin d.levelCount :=
  ⟨d.levels.idxOf (d.vertexHeight v), List.idxOf_lt_length_iff.mpr (d.vertexHeight_mem_levels v)⟩

/-- The lower cap, the event heights, and the upper cap. -/
noncomputable def levelLandmark : Fin (d.levelCount + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc d.levelHeight 1)

/-- The rank of a wire's starting landmark, including the lower cap. -/
noncomputable def layerStartIndex (w : Fin W) : Fin (d.levelCount + 2) :=
  (d.start w).elim 0 (fun v => (d.levelIndex v).castSucc.succ)

/-- The rank of a wire's finishing landmark, including the upper cap. -/
noncomputable def layerFinishIndex (w : Fin W) : Fin (d.levelCount + 2) :=
  (d.finish w).elim (Fin.last (d.levelCount + 1)) (fun v => (d.levelIndex v).castSucc.succ)

/-- An open gap between consecutive event heights or caps. -/
noncomputable def levelGap (i : Fin (d.levelCount + 1)) : Set ℝ :=
  Set.Ioo (d.levelLandmark i.castSucc) (d.levelLandmark i.succ)

structure LayerCuts where
  height : Fin (d.levelCount + 1) → ℝ
  in_gap : ∀ i, height i ∈ d.levelGap i

/-- The cut wire IDs and exact slot decompositions used to compose a sheet.
Each layer retains its original vertex IDs and ordered input/output blocks
for incidence readback. -/
structure LayerSweep where
  cuts : d.LayerCuts
  wires : Fin (d.levelCount + 1) → List (Fin W)
  ordered : ∀ i, d.OrderedCut (cuts.height i) (wires i)
  layer : ∀ i : Fin d.levelCount, d.LayerSlice (d.levelHeight i)
    (cuts.height i.castSucc) (cuts.height i.succ)
  before : ∀ i, ((layer i).slots.flatMap d.slotInputs) = wires i.castSucc
  after : ∀ i, ((layer i).slots.flatMap d.slotOutputs) = wires i.succ

namespace LayerSweep

open Silmaril.RuntimeWires.Sliced

variable {d} (s : d.LayerSweep)

/-- Independently choose the execution order at each event level. -/
structure Schedule where
  order : Fin d.levelCount → List (Fin V)
  perm : ∀ i, (order i).Perm (s.layer i).vertices

def word (i : Fin (d.levelCount + 1)) : List O := (s.wires i).map d.label

/-- One geometric row, typed at its two shared cut words. -/
noncomputable def row (i : Fin d.levelCount) : Row S (s.word i.castSucc) (s.word i.succ) :=
  (s.layer i).cutRow.reindex
    (congrArg (List.map d.label) (s.before i)) (congrArg (List.map d.label) (s.after i))

/-- Compose one row per distinct height at the shared typed frontiers. -/
noncomputable def sheet : Sheet S (s.word 0) (s.word (Fin.last d.levelCount)) :=
  Sweep.joinRows s.word s.row

/-- The serial sheet for one layer, at the same shared words as its geometric row. -/
noncomputable def serialSegment (p : s.Schedule) (i : Fin d.levelCount) :
    Sheet S (s.word i.castSucc) (s.word i.succ) :=
  ((s.layer i).serializeCuts (p.order i) (p.perm i)).reindex
    (congrArg (List.map d.label) (s.before i)) (congrArg (List.map d.label) (s.after i))

end LayerSweep
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram

namespace Silmaril.RuntimeWires.Sliced.Sheet

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Glue a finite sequence of sheets along their successive typed frontiers. -/
def joinSegments {n : ℕ} (word : Fin (n + 1) → List O)
    (segment : ∀ i : Fin n, Sheet S (word i.castSucc) (word i.succ)) :
    Sheet S (word 0) (word (Fin.last n)) :=
  match n with
  | 0 => .empty _
  | _ + 1 => (segment 0).thenDo (joinSegments (word ∘ Fin.succ) (fun i => segment i.succ))

end Silmaril.RuntimeWires.Sliced.Sheet

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable (s : d.LayerSweep)

/-- Compose the serial sheets of all layers at the shared cut words. -/
noncomputable def serialSheet (p : s.Schedule) :
    Sliced.Sheet S (s.word 0) (s.word (Fin.last d.levelCount)) :=
  Sliced.Sheet.joinSegments s.word (s.serialSegment p)

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep
