module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveTrace.Rows
import Mathlib.Data.List.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveTrace

open Silmaril.RuntimeWires.Sliced Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}
variable (s : d.Sweep)

private theorem output_mem {w : Fin W} {v : Fin V} (hw : d.start w = some v) :
    w ∈ d.outputs v :=
  List.mem_ofFn.mpr ((d.output_exact v w).mp hw)

private theorem mem_output_iff (w : Fin W) (v : Fin V) :
    w ∈ d.outputs v ↔ d.start w = some v :=
  List.mem_ofFn.trans (d.output_exact v w).symm

theorem boundary_names :
    namePorts .boundary ((s.wires 0).map d.label) = (s.wires 0).map s.namedWire := by
  rw [namePorts_map _ (s.ordered 0).nodup]
  apply List.map_congr_left
  intro w hw
  simp [Diagram.Sweep.namedWire, Diagram.Sweep.origin, (s.input_mem w).mp hw]

theorem box_output_names (i : Fin V) :
    namePorts (.box i.val 0) (S.target (d.generator (d.vertexOrder i))) =
      (d.outputs (d.vertexOrder i)).map s.namedWire := by
  have nd := (s.event i).after.nodup
  rw [List.append_assoc] at nd
  have ho := (List.pairwise_append.mp (List.pairwise_append.mp nd).2.1).1
  rw [← d.output_types (d.vertexOrder i)]
  change namePorts (.box i.val 0) ((d.outputs (d.vertexOrder i)).map d.label) = _
  rw [namePorts_map _ ho]
  apply List.map_congr_left
  intro w hw
  simp [Diagram.Sweep.namedWire, Diagram.Sweep.origin, (mem_output_iff w _).mp hw]

theorem origin_injective : Function.Injective s.origin := by
  intro w z eq
  rcases hw : d.start w with _ | a <;> rcases hz : d.start z with _ | b
  · have hi : (s.wires 0).idxOf w = (s.wires 0).idxOf z :=
      WireOrigin.boundary.inj (by simpa [Diagram.Sweep.origin, hw, hz] using eq)
    exact (List.idxOf_inj ((s.input_mem w).mpr hw)).mp hi
  · simp [Diagram.Sweep.origin, hw, hz] at eq
  · simp [Diagram.Sweep.origin, hw, hz] at eq
  · have he : WireOrigin.box (d.vertexOrder.symm a).val 0 ((d.outputs a).idxOf w) =
        WireOrigin.box (d.vertexOrder.symm b).val 0 ((d.outputs b).idxOf z) := by
      simpa [Diagram.Sweep.origin, hw, hz] using eq
    obtain ⟨hi, _, hp⟩ := WireOrigin.box.inj he
    have same : a = b := d.vertexOrder.symm.injective (Fin.ext hi)
    subst b
    exact (List.idxOf_inj (output_mem hw)).mp hp

end Silmaril.RuntimeWires.Proofs.ProgressiveTrace
