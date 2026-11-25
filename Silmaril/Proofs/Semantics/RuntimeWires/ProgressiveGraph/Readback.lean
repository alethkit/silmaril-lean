module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGraph.Slicing

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGraph

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation} (d : Diagram S V W kind)

private theorem crosses_of_regular {h : ℝ} (reg : d.Regular h) {w : Fin W} (hc : d.covers w h) :
    d.crosses w h := by
  refine ⟨lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩
  · cases hs : d.start w with
    | none =>
      change endpointHeight d.vertexHeight 0 (d.start w) ≠ h
      simpa [hs, endpointHeight] using reg.inside.1.ne
    | some v => exact (start_height d hs).trans_ne (reg.avoids v)
  · cases hs : d.finish w with
    | none =>
      change h ≠ endpointHeight d.vertexHeight 1 (d.finish w)
      simpa [hs, endpointHeight] using reg.inside.2.ne
    | some v => exact (reg.avoids v).symm.trans_eq (finish_height d hs).symm

theorem regular_trace {h : ℝ} (reg : d.Regular h) {wires : List (Fin W)}
    (cut : d.OrderedCut h wires) :
    d.wireTrace ∩ {p | p.2 = h} = {p | p.2 = h ∧ p.1 ∈ wires.map (fun w => d.x w h)} := by
  ext p
  constructor
  · rintro ⟨hp, hh⟩
    obtain ⟨w, ⟨k, hk, hpoint⟩⟩ := Set.mem_iUnion.mp hp
    have hk' : k = h := (congrArg Prod.snd hpoint).trans hh
    subst k
    exact ⟨hh, List.mem_map.mpr ⟨w, (cut.exact_wires w).mpr (crosses_of_regular d reg hk),
      congrArg Prod.fst hpoint⟩⟩
  · rintro ⟨hh, hpos⟩
    obtain ⟨w, hw, hx⟩ := List.mem_map.mp hpos
    have hc := (cut.exact_wires w).mp hw
    exact ⟨Set.mem_iUnion.mpr ⟨w, h, ⟨hc.1.le, hc.2.le⟩, Prod.ext hx hh.symm⟩, hh⟩

variable {d} {v : Fin V} {lo hi : ℝ}

theorem before_word (s : d.EventSlice v lo hi) :
    s.beforeWires.map d.label =
      s.left.map d.label ++ (S.source (d.generator v) ++ s.right.map d.label) := by
  simp only [Diagram.EventSlice.beforeWires, Diagram.inputs, List.map_append, List.append_assoc,
    d.input_types]

theorem after_word (s : d.EventSlice v lo hi) :
    s.afterWires.map d.label =
      s.left.map d.label ++ (S.target (d.generator v) ++ s.right.map d.label) := by
  simp only [Diagram.EventSlice.afterWires, Diagram.outputs, List.map_append, List.append_assoc,
    d.output_types]

end Silmaril.RuntimeWires.Proofs.ProgressiveGraph
