module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Comparison
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback

public section

namespace Silmaril.RuntimeWires.Proofs.CapReadout

open ProgressiveGraph ProgressiveGraph.Diagram
open Sliced (Sheet)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : CapProfile O}

theorem readSheetAt_comparison {p q : FixedDrawing S a b}
    (h : p.drawing.CapComparison q.drawing) (s : p.drawing.LayerSweep) (t : q.drawing.LayerSweep) :
    p.readSheetAt s = q.readSheetAt t := by
  apply Sheet.cells_injective
  simpa only [FixedDrawing.readSheetAt, Sheet.cells_reindex] using (sweep_cells h s t).symm

theorem readSheet_thenDo (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    (p.thenDo q).readSheet = p.readSheet.thenDo q.readSheet := by
  apply Sheet.cells_injective
  let m := p.matching q
  let s := p.drawing.layerSweep
  let t := q.drawing.layerSweep
  let r := m.glue.layerSweep
  simp only [FixedDrawing.readSheet, FixedDrawing.readSheetAt, Sheet.cells_reindex,
    ProgressiveGluing.cells_thenDo]
  change r.sheet.cells = s.sheet.cells ++ t.sheet.cells
  simpa only [Sheet.cells_reindex, ProgressiveGluing.cells_thenDo] using
    congrArg Sheet.cells (m.sweep_concat s t r)

theorem readSheet_vertexFree (p : FixedDrawing S a b) (vertices : p.vertices = 0)
    (word : List.ofFn a.label = List.ofFn b.label) :
    p.readSheet = (Sheet.empty (S := S) (List.ofFn a.label)).reindex rfl word := by
  have count : p.drawing.levelCount = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro pos
    obtain ⟨v, _⟩ := p.drawing.vertex_at_level ⟨0, pos⟩
    exact (v.cast vertices).elim0
  apply Sheet.cells_injective
  simp only [FixedDrawing.readSheet, FixedDrawing.readSheetAt, Sheet.cells_reindex, Sheet.cells_empty,
    LayerSweep.sheet, ProgressiveGluing.cells_joinRows, List.ofFn_eq_nil_iff, count]

end Silmaril.RuntimeWires.Proofs.CapReadout
