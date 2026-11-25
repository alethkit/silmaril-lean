module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Layout
public import Silmaril.Proofs.Semantics.RuntimeWires.Polygonal.Strands

public section

namespace Silmaril.RuntimeWires.Proofs.Polygonal

open Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {slab : Slab}

private theorem wire_horizontal {floor : ℝ} (w : Through floor) {p : Point}
    (hp : p ∈ (Strand.mk (slab := slab) w.start w.finish).trace) :
    p.1 ∈ Set.Ioo floor w.limit :=
  trace_horizontal hp ⟨w.start_left, w.start_right⟩ ⟨w.finish_left, w.finish_right⟩

theorem layer_bounds {floor : ℝ} {A B : List O} (r : Layer S floor A B)
    {region : Set Point} {p : Point} (hr : region ∈ r.traces slab) (hp : p ∈ region) :
    floor < p.1 ∧ p.2 ∈ Set.Icc slab.lower slab.upper := by
  induction r with
  | empty => simp [Layer.traces] at hr
  | wire _ w rest ih =>
    rcases List.mem_cons.mp hr with rfl | h
    · exact ⟨(wire_horizontal w hp).1, trace_height hp⟩
    · exact ⟨(w.start_left.trans w.start_right).trans (ih h).1, (ih h).2⟩
  | box _ b rest ih =>
    rcases List.mem_cons.mp hr with rfl | h
    · exact ⟨b.left_bound.trans_le hp.1.1, hp.2⟩
    · exact ⟨(b.left_bound.trans b.width).trans (ih h).1, (ih h).2⟩

theorem layer_disjoint (slab : Slab) {floor : ℝ} {A B : List O} (r : Layer S floor A B) :
    (r.traces slab).Pairwise Disjoint := by
  induction r with
  | empty => exact .nil
  | wire _ w rest ih =>
    refine .cons (fun region hr => Set.disjoint_left.mpr fun p hp hq => ?_) ih
    exact (not_lt_of_ge (wire_horizontal w hp).2.le) (layer_bounds rest hr hq).1
  | box _ b rest ih =>
    refine .cons (fun region hr => Set.disjoint_left.mpr fun p hp hq => ?_) ih
    exact (not_lt_of_ge hp.1.2) (layer_bounds rest hr hq).1

theorem trace_start (s : Strand slab) : (s.start, slab.lower) ∈ s.trace :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [Strand.point, interpolate]⟩

theorem trace_finish (s : Strand slab) : (s.finish, slab.upper) ∈ s.trace :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [Strand.point, interpolate]⟩

theorem input_covered {floor x : ℝ} {A B : List O} (r : Layer S floor A B)
    (h : x ∈ r.inputs.frontier.positions) :
    ∃ region ∈ r.traces slab, (x, slab.lower) ∈ region := by
  induction r with
  | empty =>
    change x ∈ [] at h
    exact False.elim (List.not_mem_nil h)
  | wire _ w rest ih =>
    change x ∈ w.start :: rest.inputs.frontier.positions at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, trace_start (Strand.mk (slab := slab) w.start w.finish)⟩
    · obtain ⟨region, hr, hx⟩ := ih h
      exact ⟨region, List.mem_cons_of_mem _ hr, hx⟩
  | box _ b rest ih =>
    change x ∈ b.input.positions ++ rest.inputs.frontier.positions at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨lo, hi⟩ := b.input_inside x h
      exact ⟨_, List.mem_cons_self, ⟨⟨lo.le, hi.le⟩, ⟨le_rfl, slab.increasing.le⟩⟩⟩
    · obtain ⟨region, hr, hx⟩ := ih h
      exact ⟨region, List.mem_cons_of_mem _ hr, hx⟩

theorem output_covered {floor x : ℝ} {A B : List O} (r : Layer S floor A B)
    (h : x ∈ r.outputs.frontier.positions) :
    ∃ region ∈ r.traces slab, (x, slab.upper) ∈ region := by
  induction r with
  | empty =>
    change x ∈ [] at h
    exact False.elim (List.not_mem_nil h)
  | wire _ w rest ih =>
    change x ∈ w.finish :: rest.outputs.frontier.positions at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, trace_finish (Strand.mk (slab := slab) w.start w.finish)⟩
    · obtain ⟨region, hr, hx⟩ := ih h
      exact ⟨region, List.mem_cons_of_mem _ hr, hx⟩
  | box _ b rest ih =>
    change x ∈ b.output.positions ++ rest.outputs.frontier.positions at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨lo, hi⟩ := b.output_inside x h
      exact ⟨_, List.mem_cons_self, ⟨⟨lo.le, hi.le⟩, ⟨slab.increasing.le, le_rfl⟩⟩⟩
    · obtain ⟨region, hr, hx⟩ := ih h
      exact ⟨region, List.mem_cons_of_mem _ hr, hx⟩

end Silmaril.RuntimeWires.Proofs.Polygonal
