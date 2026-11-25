module

public import Silmaril.Semantics.RuntimeWires.TiedHeightTrace.Defs
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.TiedHeightTrace

open Silmaril.RuntimeWires.ProgressiveGraph Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable (s : d.LayerSweep)

private theorem mem_output_iff (w : Fin W) (v : Fin V) :
    w ∈ d.outputs v ↔ d.start w = some v :=
  List.mem_ofFn.trans (d.output_exact v w).symm

theorem boundary_names :
    namePorts .boundary (s.word 0) = (s.wires 0).map s.namedWire := by
  rw [Diagram.LayerSweep.word, namePorts_map _ (s.ordered 0).nodup]
  apply List.map_congr_left
  intro w hw
  simp [Diagram.LayerSweep.namedWire, Diagram.LayerSweep.origin, (s.input_mem w).mp hw]

theorem box_output_names (i : Fin d.levelCount) (v : Fin V) (hv : v ∈ (s.layer i).vertices) :
    namePorts (.box i.val ((s.layer i).vertices.idxOf v)) (S.target (d.generator v)) =
      (d.outputs v).map s.namedWire := by
  have slot : Sum.inr v ∈ (s.layer i).slots :=
    ((s.layer i).exact_slots _).mpr (((s.layer i).vertices_exact v).mp hv)
  have nd : (d.outputs v).Nodup :=
    (List.nodup_flatMap.mp (s.layer i).after.nodup).1 _ slot
  have rank := (s.vertex_mem i v).mp hv
  have ordinal : s.boxOrdinal v = (s.layer i).vertices.idxOf v :=
    congrArg (fun j => (s.layer j).vertices.idxOf v) rank
  rw [← d.output_types v]
  change namePorts _ ((d.outputs v).map d.label) = _
  rw [namePorts_map _ nd]
  apply List.map_congr_left
  intro w hw
  simp [Diagram.LayerSweep.namedWire, Diagram.LayerSweep.origin, (mem_output_iff w v).mp hw, rank,
    ordinal]

theorem origin_injective : Function.Injective s.origin := by
  intro w z eq
  rcases hw : d.start w with _ | a <;> rcases hz : d.start z with _ | b
  · have hi : (s.wires 0).idxOf w = (s.wires 0).idxOf z :=
      WireOrigin.boundary.inj (by simpa [Diagram.LayerSweep.origin, hw, hz] using eq)
    exact (List.idxOf_inj ((s.input_mem w).mpr hw)).mp hi
  · simp [Diagram.LayerSweep.origin, hw, hz] at eq
  · simp [Diagram.LayerSweep.origin, hw, hz] at eq
  · have he : WireOrigin.box (d.levelIndex a).val (s.boxOrdinal a) ((d.outputs a).idxOf w) =
        WireOrigin.box (d.levelIndex b).val (s.boxOrdinal b) ((d.outputs b).idxOf z) := by
      simpa [Diagram.LayerSweep.origin, hw, hz] using eq
    obtain ⟨row, box, port⟩ := WireOrigin.box.inj he
    have sameLevel : d.levelIndex a = d.levelIndex b := Fin.ext row
    unfold Diagram.LayerSweep.boxOrdinal at box
    rw [← sameLevel] at box
    have sameVertex : a = b := (List.idxOf_inj ((s.vertex_mem _ a).mpr rfl)).mp box
    subst b
    exact (List.idxOf_inj ((mem_output_iff w a).mpr hw)).mp port

end Silmaril.RuntimeWires.Proofs.TiedHeightTrace
