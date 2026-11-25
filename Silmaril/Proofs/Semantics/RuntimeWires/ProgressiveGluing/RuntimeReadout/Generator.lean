module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback

public section

namespace Silmaril.RuntimeWires.Proofs.RuntimeReadout

open ProgressiveGraph ProgressiveGraph.Diagram
open Sliced (Row Sheet)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}
variable (p : FixedDrawing S a b) (v : Fin p.vertices)
variable (only : ∀ j, j = v)

include only in
private theorem one_level : p.drawing.levelCount = 1 := by
  have heights : Finset.univ.image p.drawing.vertexHeight = {p.drawing.vertexHeight v} := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨j, h⟩ => h.symm.trans (congrArg p.drawing.vertexHeight (only j)),
      fun h => ⟨v, h.symm⟩⟩
  simp only [Diagram.levelCount, Diagram.levels, heights, Finset.sort_singleton, List.length_cons, List.length_nil]

include only in
private theorem event_slots (s : p.drawing.LayerSweep)
    (noThrough : ∀ w, ¬ p.drawing.crosses w (p.drawing.vertexHeight v))
    (i : Fin p.drawing.levelCount) : (s.layer i).slots = [.inr v] := by
  obtain ⟨j, hj⟩ := p.drawing.vertex_at_level i
  have height : p.drawing.levelHeight i = p.drawing.vertexHeight v :=
    hj.symm.trans (congrArg p.drawing.vertexHeight (only j))
  have same (z : LayerSlot p.vertices p.wires) : z ∈ (s.layer i).slots ↔ z ∈ [.inr v] := by
    rw [(s.layer i).exact_slots, height]
    cases z with
    | inl w => simpa only [Diagram.atLayer, List.mem_singleton, Sum.inl_ne_inr, iff_false] using noThrough w
    | inr k => simp only [only k, Diagram.atLayer, List.mem_singleton]
  have nodup := (s.layer i).ordered.imp
    (fun lt => ne_of_apply_ne (p.drawing.slotX (p.drawing.levelHeight i)) (ne_of_lt lt))
  have perm := (List.perm_ext_iff_of_nodup nodup (List.nodup_singleton _)).mpr same
  exact List.perm_singleton.mp perm

private theorem generator_cells (e : S.Edge) : (Sheet.generator e).cells = [[.inr e]] := by
  simp only [Sheet.generator, Sheet.cells_reindex, Sheet.cells_cons, Sheet.cells_empty, Row.cells_box]
  rw [show (Row.empty (S := S)).cells = [] from Row.cells_straight []]

include only in
theorem read_generator (s : p.drawing.LayerSweep) (e : S.Edge)
    (generator : p.drawing.generator v = e)
    (noThrough : ∀ w, ¬ p.drawing.crosses w (p.drawing.vertexHeight v))
    (input : S.source e = List.ofFn a.label) (output : S.target e = List.ofFn b.label) :
    p.readSheetAt s = (Sheet.generator e).reindex input output := by
  apply Sheet.cells_injective
  simp only [FixedDrawing.readSheetAt, Sheet.cells_reindex, LayerSweep.sheet,
    ProgressiveGluing.cells_joinRows, generator_cells]
  have row (i : Fin p.drawing.levelCount) : (s.row i).cells = [.inr e] := by
    rw [ProgressiveGluing.sweep_row_cells, event_slots p v only s noThrough i]
    change (Row.box (p.drawing.generator v) .empty).cells = _
    rw [Row.cells_box, generator, show (Row.empty (S := S)).cells = [] from Row.cells_straight []]
  rw [show (fun i => (s.row i).cells) = fun _ => [.inr e] from funext row]
  rw [List.ofFn_congr (one_level p v only)]
  simp [List.ofFn_succ]

end Silmaril.RuntimeWires.Proofs.RuntimeReadout
