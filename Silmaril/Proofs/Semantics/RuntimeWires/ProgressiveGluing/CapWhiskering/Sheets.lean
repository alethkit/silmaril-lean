module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Layers
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback

public section

namespace Silmaril.RuntimeWires.Proofs.CapWhiskering

open ProgressiveGraph ProgressiveGraph.Diagram
open Sliced (Row Sheet)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}

private theorem padLeft_cells {A B : List O} (W : List O) (p : Sheet S A B) :
    (p.padLeft W).cells = p.cells.map (W.map Sum.inl ++ ·) := by
  induction p with
  | empty => simp only [Sheet.padLeft, Sheet.cells_empty, List.map_nil]
  | cons row p ih =>
    simp only [Sheet.padLeft, Sheet.cells_cons, Row.cells_pass, List.map_cons, ih]

private theorem padRight_cells {A B : List O} (p : Sheet S A B) (W : List O) :
    (p.padRight W).cells = p.cells.map (· ++ W.map Sum.inl) := by
  induction p with
  | empty => simp only [Sheet.padRight, Sheet.cells_empty, List.map_nil]
  | cons row p ih =>
    simp only [Sheet.padRight, Sheet.cells_cons, Row.cells_beside, Row.cells_straight, List.map_cons, ih]

private theorem sheet_cells (side : ActiveStrip) (p : FixedDrawing S a.profile b.profile)
    (idle : FixedCap S) (s : p.drawing.LayerSweep) (t : (side.placeDrawing p idle).drawing.LayerSweep) :
    t.sheet.cells = match side with
      | .left => s.sheet.cells.map (· ++ idle.types.map Sum.inl)
      | .right => s.sheet.cells.map (idle.types.map Sum.inl ++ ·) := by
  have rows := congrArg List.ofFn (funext (row_cells side p idle s t))
  have same := (List.ofFn_congr (level_count side p idle) (fun i => (t.row i).cells)).trans rows
  cases side <;>
    simpa only [LayerSweep.sheet, ProgressiveGluing.cells_joinRows, List.map_ofFn, Function.comp_def] using same

theorem read_left (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S)
    (s : p.drawing.LayerSweep) (t : (ActiveStrip.left.placeDrawing p idle).drawing.LayerSweep) :
    (ActiveStrip.left.placeDrawing p idle).readSheetAt t =
      ((p.readSheetAt s).padRight idle.types).reindex
        (ActiveStrip.left.adjoin_labels a idle).symm (ActiveStrip.left.adjoin_labels b idle).symm := by
  apply Sheet.cells_injective
  calc
    _ = t.sheet.cells := Sheet.cells_reindex _ _ t.sheet
    _ = s.sheet.cells.map (· ++ idle.types.map Sum.inl) := sheet_cells .left p idle s t
    _ = ((p.readSheetAt s).padRight idle.types).cells := by
      rw [padRight_cells]
      exact congrArg (List.map (· ++ idle.types.map Sum.inl)) (Sheet.cells_reindex _ _ s.sheet).symm
    _ = _ := (Sheet.cells_reindex _ _ ((p.readSheetAt s).padRight idle.types)).symm

theorem read_right (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S)
    (s : p.drawing.LayerSweep) (t : (ActiveStrip.right.placeDrawing p idle).drawing.LayerSweep) :
    (ActiveStrip.right.placeDrawing p idle).readSheetAt t =
      ((p.readSheetAt s).padLeft idle.types).reindex
        (ActiveStrip.right.adjoin_labels a idle).symm (ActiveStrip.right.adjoin_labels b idle).symm := by
  apply Sheet.cells_injective
  calc
    _ = t.sheet.cells := Sheet.cells_reindex _ _ t.sheet
    _ = s.sheet.cells.map (idle.types.map Sum.inl ++ ·) := sheet_cells .right p idle s t
    _ = ((p.readSheetAt s).padLeft idle.types).cells := by
      rw [padLeft_cells]
      exact congrArg (List.map (idle.types.map Sum.inl ++ ·)) (Sheet.cells_reindex _ _ s.sheet).symm
    _ = _ := (Sheet.cells_reindex _ _ ((p.readSheetAt s).padLeft idle.types)).symm

end Silmaril.RuntimeWires.Proofs.CapWhiskering
