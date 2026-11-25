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

include pair

private theorem endpoint_between {cap : ℝ} (hc : cap ∉ Set.Icc lo hi)
    {p : Option (Fin V)} (hp : endpointHeight d.vertexHeight cap p ∈ Set.Icc lo hi) :
    p = some v ∨ p = some z := by
  cases p with
  | none => exact (hc hp).elim
  | some j =>
    rcases pair.only j hp with he | he
    · exact Or.inl (congrArg some he)
    · exact Or.inr (congrArg some he)

private theorem start_between {w : Fin W} (h : d.lower w ∈ Set.Icc lo hi) :
    d.start w = some v ∨ d.start w = some z :=
  endpoint_between pair (fun h => pair.lo_inside.not_ge h.1) h

private theorem finish_between {w : Fin W} (h : d.upper w ∈ Set.Icc lo hi) :
    d.finish w = some v ∨ d.finish w = some z :=
  endpoint_between pair (fun h => pair.hi_inside.not_ge h.2) h

private theorem start_at {w : Fin W} (h : d.start w = some v ∨ d.start w = some z) :
    d.lower w = d.vertexHeight v :=
  h.elim start_height (fun hs => (start_height hs).trans pair.same_height)

private theorem finish_at {w : Fin W} (h : d.finish w = some v ∨ d.finish w = some z) :
    d.upper w = d.vertexHeight v :=
  h.elim finish_height (fun hs => (finish_height hs).trans pair.same_height)

private theorem lower_of_left {w : Fin W} (h : d.lower w < d.vertexHeight v) : d.lower w < lo := by
  by_contra! hn
  exact h.ne (start_at pair (start_between pair ⟨hn, h.le.trans pair.above.le⟩))

private theorem upper_of_right {w : Fin W} (h : d.vertexHeight v < d.upper w) : hi < d.upper w := by
  by_contra! hn
  exact h.ne (finish_at pair (finish_between pair ⟨pair.below.le.trans h.le, hn⟩)).symm

theorem before_classify (w : Fin W) :
    d.crosses w lo ↔ d.crosses w (d.vertexHeight v) ∨
      w ∈ d.inputs v ∨ w ∈ d.inputs z := by
  rw [input_mem, input_mem]
  constructor
  · intro h
    by_cases ht : d.vertexHeight v < d.upper w
    · exact Or.inl ⟨h.1.trans pair.below, ht⟩
    · exact Or.inr (finish_between pair ⟨h.2.le, (le_of_not_gt ht).trans pair.above.le⟩)
  · rintro (h | h)
    · exact ⟨lower_of_left pair h.1, pair.below.trans h.2⟩
    · have ht := finish_at pair h
      have hp : d.lower w < d.vertexHeight v := ht ▸ (d.wire w).increasing
      exact ⟨lower_of_left pair hp, ht ▸ pair.below⟩

theorem after_classify (w : Fin W) :
    d.crosses w hi ↔ d.crosses w (d.vertexHeight v) ∨
      w ∈ d.outputs v ∨ w ∈ d.outputs z := by
  rw [output_mem, output_mem]
  constructor
  · intro h
    by_cases ht : d.lower w < d.vertexHeight v
    · exact Or.inl ⟨ht, pair.above.trans h.2⟩
    · exact Or.inr (start_between pair ⟨pair.below.le.trans (le_of_not_gt ht), h.1.le⟩)
  · rintro (h | h)
    · exact ⟨h.1.trans pair.above, upper_of_right pair h.2⟩
    · have ht := start_at pair h
      have hp : d.vertexHeight v < d.upper w := ht ▸ (d.wire w).increasing
      exact ⟨ht ▸ pair.above, upper_of_right pair hp⟩

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

include pair

theorem incident_disjoint :
    List.Disjoint (d.inputs v ++ d.outputs v) (d.inputs z ++ d.outputs z) := by
  intro w hw hz
  have different : v ≠ z := ne_of_apply_ne d.vertexX pair.left_to_right.ne
  rcases List.mem_append.mp hw with hv | hv <;> rcases List.mem_append.mp hz with hz | hz
  · exact different (Option.some.inj (((input_mem v w).mp hv).symm.trans ((input_mem z w).mp hz)))
  · have ha := start_height ((output_mem z w).mp hz)
    have hb := finish_height ((input_mem v w).mp hv)
    exact (d.wire w).increasing.ne (ha.trans (pair.same_height.trans hb.symm))
  · have ha := start_height ((output_mem v w).mp hv)
    have hb := finish_height ((input_mem z w).mp hz)
    exact (d.wire w).increasing.ne (ha.trans (pair.same_height.symm.trans hb.symm))
  · exact different (Option.some.inj (((output_mem v w).mp hv).symm.trans ((output_mem z w).mp hz)))

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous
