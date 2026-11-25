module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Defs
import Mathlib.Data.List.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable {d : Diagram S V W kind} {v z : Fin V} {lo hi : ℝ}
variable (pair : d.IsolatesPair v z lo hi)

theorem input_mem (j : Fin V) (w : Fin W) : w ∈ d.inputs j ↔ d.finish w = some j :=
  List.mem_ofFn.trans (d.input_exact j w).symm

theorem output_mem (j : Fin V) (w : Fin W) : w ∈ d.outputs j ↔ d.start w = some j :=
  List.mem_ofFn.trans (d.output_exact j w).symm

theorem start_height {w : Fin W} {j : Fin V} (h : d.start w = some j) :
    d.lower w = d.vertexHeight j := by
  simp [Diagram.lower, endpointHeight, h]

theorem finish_height {w : Fin W} {j : Fin V} (h : d.finish w = some j) :
    d.upper w = d.vertexHeight j := by
  simp [Diagram.upper, endpointHeight, h]

section Layer

variable {height : ℝ} (layer : d.IsolatesLayer height lo hi)
include layer

private theorem endpoint_between {cap : ℝ} (hc : cap ∉ Set.Icc lo hi)
    {p : Option (Fin V)} (hp : endpointHeight d.vertexHeight cap p ∈ Set.Icc lo hi) :
    ∃ j, p = some j ∧ d.vertexHeight j = height := by
  cases p with
  | none => exact (hc hp).elim
  | some j => exact ⟨j, rfl, layer.only_height j hp⟩

private theorem start_between {w : Fin W} (h : d.lower w ∈ Set.Icc lo hi) :
    ∃ j, d.start w = some j ∧ d.vertexHeight j = height :=
  endpoint_between layer (fun h => layer.lo_inside.not_ge h.1) h

private theorem finish_between {w : Fin W} (h : d.upper w ∈ Set.Icc lo hi) :
    ∃ j, d.finish w = some j ∧ d.vertexHeight j = height :=
  endpoint_between layer (fun h => layer.hi_inside.not_ge h.2) h

private theorem lower_of_left {w : Fin W} (h : d.lower w < height) : d.lower w < lo := by
  by_contra! hn
  obtain ⟨j, hj, he⟩ := start_between layer ⟨hn, h.le.trans layer.above.le⟩
  exact h.ne ((start_height hj).trans he)

private theorem upper_of_right {w : Fin W} (h : height < d.upper w) : hi < d.upper w := by
  by_contra! hn
  obtain ⟨j, hj, he⟩ := finish_between layer ⟨layer.below.le.trans h.le, hn⟩
  exact h.ne ((finish_height hj).trans he).symm

theorem layer_before_classify (w : Fin W) :
    d.crosses w lo ↔ d.crosses w height ∨ ∃ j, d.vertexHeight j = height ∧ w ∈ d.inputs j := by
  constructor
  · intro h
    by_cases ht : height < d.upper w
    · exact Or.inl ⟨h.1.trans layer.below, ht⟩
    · obtain ⟨j, hj, he⟩ := finish_between layer ⟨h.2.le, (le_of_not_gt ht).trans layer.above.le⟩
      exact Or.inr ⟨j, he, (input_mem j w).mpr hj⟩
  · rintro (h | ⟨j, hj, hw⟩)
    · exact ⟨lower_of_left layer h.1, layer.below.trans h.2⟩
    · have ht := (finish_height ((input_mem j w).mp hw)).trans hj
      have hp : d.lower w < height := ht ▸ (d.wire w).increasing
      exact ⟨lower_of_left layer hp, ht ▸ layer.below⟩

theorem layer_after_classify (w : Fin W) :
    d.crosses w hi ↔ d.crosses w height ∨ ∃ j, d.vertexHeight j = height ∧ w ∈ d.outputs j := by
  constructor
  · intro h
    by_cases ht : d.lower w < height
    · exact Or.inl ⟨ht, layer.above.trans h.2⟩
    · obtain ⟨j, hj, he⟩ := start_between layer ⟨layer.below.le.trans (le_of_not_gt ht), h.1.le⟩
      exact Or.inr ⟨j, he, (output_mem j w).mpr hj⟩
  · rintro (h | ⟨j, hj, hw⟩)
    · exact ⟨h.1.trans layer.above, upper_of_right layer h.2⟩
    · have ht := (start_height ((output_mem j w).mp hw)).trans hj
      have hp : height < d.upper w := ht ▸ (d.wire w).increasing
      exact ⟨ht ▸ layer.above, upper_of_right layer hp⟩

end Layer

include pair

private theorem pair_ports (port : Fin V → List (Fin W)) (w : Fin W) :
    (∃ j, d.vertexHeight j = d.vertexHeight v ∧ w ∈ port j) ↔ w ∈ port v ∨ w ∈ port z := by
  constructor
  · rintro ⟨j, hj, hw⟩
    rcases pair.only j ⟨pair.below.le.trans_eq hj.symm, hj.trans_le pair.above.le⟩ with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  · rintro (hw | hw)
    · exact ⟨v, rfl, hw⟩
    · exact ⟨z, pair.same_height, hw⟩

theorem before_classify (w : Fin W) :
    d.crosses w lo ↔ d.crosses w (d.vertexHeight v) ∨ w ∈ d.inputs v ∨ w ∈ d.inputs z :=
  (layer_before_classify (pair.toLayer) w).trans (or_congr Iff.rfl (pair_ports pair d.inputs w))

theorem after_classify (w : Fin W) :
    d.crosses w hi ↔ d.crosses w (d.vertexHeight v) ∨ w ∈ d.outputs v ∨ w ∈ d.outputs z :=
  (layer_after_classify (pair.toLayer) w).trans (or_congr Iff.rfl (pair_ports pair d.outputs w))

omit pair

/-- Wires with ordered positions at the event keep that order to the cut.
At the event itself even two endpoint-only wires have distinct coordinates. -/
theorem order_to_cut {h k : ℝ} {a b : Fin W}
    (a_event : d.covers a h) (b_event : d.covers b h)
    (a_cut : d.crosses a k) (b_cut : d.crosses b k)
    (ordered : d.x a h < d.x b h) :
    d.x a k < d.x b k := by
  have covered {w : Fin W} (he : d.covers w h) (hc : d.crosses w k) {y : ℝ}
      (hy : y ∈ Set.uIcc h k) : d.covers w y :=
    ⟨(le_min he.1 hc.1.le).trans hy.1, hy.2.trans (max_le he.2 hc.2.le)⟩
  have interior {y : ℝ} (hy : y ∈ Set.uIcc h k) (hn : y ≠ h) : d.crosses a y := by
    rcases le_total h k with hk | hk
    · rw [Set.uIcc_of_le hk] at hy
      exact ⟨a_event.1.trans_lt (lt_of_le_of_ne hy.1 hn.symm), hy.2.trans_lt a_cut.2⟩
    · rw [Set.uIcc_of_ge hk] at hy
      exact ⟨a_cut.1.trans_le hy.1, (lt_of_le_of_ne hy.2 hn).trans_le a_event.2⟩
  have distinct : a ≠ b := ne_of_apply_ne (fun w => d.x w h) (ne_of_lt ordered)
  refine Diagram.order_across (fun _ hy => ⟨covered a_event a_cut hy, covered b_event b_cut hy⟩)
    (fun y hy => ?_) ordered
  by_cases he : y = h
  · exact he.symm ▸ ordered.ne
  · exact d.separated distinct (interior hy he) (covered b_event b_cut hy)

/-- A list with points at the central height and with a strict order at the cut. -/
structure Block (d : Diagram S V W kind) (event cut : ℝ) (ids : List (Fin W)) : Prop where
  covers : ∀ w ∈ ids, d.covers w event
  crosses : ∀ w ∈ ids, d.crosses w cut
  ordered : ids.Pairwise (fun a b => d.x a cut < d.x b cut)

theorem Block.append {event cut : ℝ} {l r : List (Fin W)}
    (a : Block d event cut l) (b : Block d event cut r)
    (h : ∀ w ∈ l, ∀ z ∈ r, d.x w event < d.x z event) :
    Block d event cut (l ++ r) := by
  exact ⟨fun w hw => (List.mem_append.mp hw).elim (a.covers w) (b.covers w),
    fun w hw => (List.mem_append.mp hw).elim (a.crosses w) (b.crosses w),
    List.pairwise_append.mpr ⟨a.ordered, b.ordered, fun w hw z hz =>
      order_to_cut (a.covers w hw) (b.covers z hz) (a.crosses w hw) (b.crosses z hz) (h w hw z hz)⟩⟩

theorem layer_incoming {height : ℝ} (layer : d.IsolatesLayer height lo hi) {j : Fin V}
    (at_height : d.vertexHeight j = height) : Block d height lo (d.inputs j) := by
  have crosses (w : Fin W) (hw : w ∈ d.inputs j) : d.crosses w lo :=
    (layer_before_classify layer w).mpr (Or.inr ⟨j, at_height, hw⟩)
  refine ⟨fun w hw => ?_, crosses, List.pairwise_ofFn.mpr ?_⟩
  · have upper := (finish_height ((input_mem j w).mp hw)).trans at_height
    exact ⟨(crosses w hw).1.le.trans layer.below.le, upper.ge⟩
  · intro a b hab
    have ha := crosses _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
    have hb := crosses _ (List.mem_ofFn.mpr ⟨b, rfl⟩)
    exact d.input_order j hab ha.1 hb.1 (layer.below.trans_eq at_height.symm)

theorem layer_outgoing {height : ℝ} (layer : d.IsolatesLayer height lo hi) {j : Fin V}
    (at_height : d.vertexHeight j = height) : Block d height hi (d.outputs j) := by
  have crosses (w : Fin W) (hw : w ∈ d.outputs j) : d.crosses w hi :=
    (layer_after_classify layer w).mpr (Or.inr ⟨j, at_height, hw⟩)
  refine ⟨fun w hw => ?_, crosses, List.pairwise_ofFn.mpr ?_⟩
  · have lower := (start_height ((output_mem j w).mp hw)).trans at_height
    exact ⟨lower.le, layer.above.le.trans (crosses w hw).2.le⟩
  · intro a b hab
    have ha := crosses _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
    have hb := crosses _ (List.mem_ofFn.mpr ⟨b, rfl⟩)
    exact d.output_order j hab (at_height.trans_lt layer.above) ha.2 hb.2

theorem same_level_incident_disjoint (different : v ≠ z)
    (same_height : d.vertexHeight z = d.vertexHeight v) :
    List.Disjoint (d.inputs v ++ d.outputs v) (d.inputs z ++ d.outputs z) := by
  intro w hw hz
  rcases List.mem_append.mp hw with hv | hv <;> rcases List.mem_append.mp hz with hz | hz
  · exact different (Option.some.inj (((input_mem v w).mp hv).symm.trans ((input_mem z w).mp hz)))
  · have ha := start_height ((output_mem z w).mp hz)
    have hb := finish_height ((input_mem v w).mp hv)
    exact (d.wire w).increasing.ne (ha.trans (same_height.trans hb.symm))
  · have ha := start_height ((output_mem v w).mp hv)
    have hb := finish_height ((input_mem z w).mp hz)
    exact (d.wire w).increasing.ne (ha.trans (same_height.symm.trans hb.symm))
  · exact different (Option.some.inj (((output_mem v w).mp hv).symm.trans ((output_mem z w).mp hz)))

include pair

theorem incident_disjoint :
    List.Disjoint (d.inputs v ++ d.outputs v) (d.inputs z ++ d.outputs z) :=
  same_level_incident_disjoint (ne_of_apply_ne d.vertexX pair.left_to_right.ne) pair.same_height

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous
