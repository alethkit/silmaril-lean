module

public import Silmaril.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveCutChoice.Thms
import Mathlib.Tactic.Linarith

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {moved other : Fin V} {s : d.NullarySlide moved}
variable {side : NullarySlide.Side} (c : s.Crossing other side)

include c in
theorem different : other ≠ moved := by
  intro same
  subst other
  have h := c.horizontal
  cases side <;> exact lt_irrefl _ h

include c in
theorem height_other {h : ℝ} (hw : h ∈ Set.Icc s.bottom s.top) :
    (s.atHeight h hw).vertexHeight other = d.vertexHeight other :=
  s.stationary_height hw (different c)

theorem center_height_left :
    c.tied.vertexHeight (side.leftVertex moved other) = d.vertexHeight other := by
  cases side
  · exact s.moved_height _
  · exact height_other c _

theorem center_height_right :
    c.tied.vertexHeight (side.rightVertex moved other) = d.vertexHeight other := by
  cases side
  · exact height_other c _
  · exact s.moved_height _

theorem tied_pair :
    c.tied.IsolatesPair (side.leftVertex moved other) (side.rightVertex moved other)
      c.lowerCut c.upperCut := by
  refine ⟨(center_height_right c).trans (center_height_left c).symm, c.horizontal, c.lower_inside,
    ?_, ?_, c.upper_inside, ?_⟩
  · rw [center_height_left c]
    exact c.lower_bottom.trans (c.bottom_early.trans c.early_other)
  · rw [center_height_left c]
    exact c.other_late.trans (c.late_top.trans c.top_upper)
  · intro j band
    have only : j = moved ∨ j = other := by
      by_cases eq : j = moved
      · exact Or.inl eq
      · apply c.only
        rwa [show c.tied.vertexHeight j = d.vertexHeight j from s.stationary_height _ eq] at band
    cases side
    · exact only
    · exact only.symm

private theorem atHeight_eq {a b : ℝ} (ha : a ∈ Set.Icc s.bottom s.top)
    (hb : b ∈ Set.Icc s.bottom s.top) (same : a = b) : s.atHeight a ha = s.atHeight b hb := by
  subst b
  rfl

theorem tied_frame : ∃ t, s.frame t = c.tied := by
  obtain ⟨t, atCenter⟩ := s.hits_height
    (show d.vertexHeight other ∈ Set.Icc s.bottom s.top from
      ⟨(c.bottom_early.trans c.early_other).le, (c.other_late.trans c.late_top).le⟩)
  exact ⟨t, atHeight_eq (s.height_mem t) _ atCenter⟩

private theorem exclude {h : ℝ} (valid : h ∈ Set.Icc s.bottom s.top)
    {lo hi : ℝ} (hl : c.lowerCut ≤ lo) (hh : hi ≤ c.upperCut)
    {j : Fin V} (hw : (s.atHeight h valid).vertexHeight j ∈ Set.Icc lo hi) : j = moved ∨ j = other := by
  by_cases eq : j = moved
  · exact Or.inl eq
  · rw [s.stationary_height valid eq] at hw
    exact c.only j ⟨hl.trans hw.1, hw.2.trans hh⟩

theorem early_first : s.initial.Isolates moved c.lowerCut c.earlyCut := by
  have hm : s.initial.vertexHeight moved = s.bottom := s.moved_height _
  have ho : s.initial.vertexHeight other = d.vertexHeight other := height_other c _
  refine ⟨c.lower_inside, hm ▸ c.lower_bottom, hm ▸ c.bottom_early,
    c.early_other.trans (c.other_late.trans (c.late_top.trans (c.top_upper.trans c.upper_inside))), ?_⟩
  intro j hj
  rcases exclude c _ le_rfl (c.early_other.trans (c.other_late.trans (c.late_top.trans c.top_upper))).le hj with eq | eq
  · exact eq
  · subst j
    exact (c.early_other.not_ge (ho ▸ hj.2)).elim

theorem early_second : s.initial.Isolates other c.earlyCut c.upperCut := by
  have hm : s.initial.vertexHeight moved = s.bottom := s.moved_height _
  have ho : s.initial.vertexHeight other = d.vertexHeight other := height_other c _
  have aside := c.lower_bottom.trans c.bottom_early
  refine ⟨c.lower_inside.trans aside, ho ▸ c.early_other,
    ho ▸ c.other_late.trans (c.late_top.trans c.top_upper), c.upper_inside, ?_⟩
  intro j hj
  rcases exclude c _ aside.le le_rfl hj with eq | eq
  · subst j
    exact (c.bottom_early.not_ge (hm ▸ hj.1)).elim
  · exact eq

theorem late_first : s.terminal.Isolates other c.lowerCut c.lateCut := by
  have hm : s.terminal.vertexHeight moved = s.top := s.moved_height _
  have ho : s.terminal.vertexHeight other = d.vertexHeight other := height_other c _
  have aside := c.late_top.trans c.top_upper
  refine ⟨c.lower_inside, ho ▸ c.lower_bottom.trans (c.bottom_early.trans c.early_other),
    ho ▸ c.other_late, aside.trans c.upper_inside, ?_⟩
  intro j hj
  rcases exclude c _ le_rfl aside.le hj with eq | eq
  · subst j
    exact (c.late_top.not_ge (hm ▸ hj.2)).elim
  · exact eq

theorem late_second : s.terminal.Isolates moved c.lateCut c.upperCut := by
  have hm : s.terminal.vertexHeight moved = s.top := s.moved_height _
  have ho : s.terminal.vertexHeight other = d.vertexHeight other := height_other c _
  have aside := c.lower_bottom.trans (c.bottom_early.trans (c.early_other.trans c.other_late))
  refine ⟨c.lower_inside.trans aside, hm ▸ c.late_top, hm ▸ c.top_upper, c.upper_inside, ?_⟩
  intro j hj
  rcases exclude c _ aside.le le_rfl hj with eq | eq
  · exact eq
  · subst j
    exact (c.other_late.not_ge (ho ▸ hj.1)).elim

private theorem endpoint_cases (cap : ℝ) (outside : cap < c.lowerCut ∨ c.upperCut < cap)
    (endpoint : Option (Fin V)) :
    endpointHeight c.tied.vertexHeight cap endpoint < c.lowerCut ∨
      endpointHeight c.tied.vertexHeight cap endpoint = d.vertexHeight other ∨
      c.upperCut < endpointHeight c.tied.vertexHeight cap endpoint := by
  cases endpoint with
  | none => exact outside.imp_right Or.inr
  | some j =>
    by_cases low : c.tied.vertexHeight j < c.lowerCut
    · exact Or.inl low
    by_cases high : c.upperCut < c.tied.vertexHeight j
    · exact Or.inr (Or.inr high)
    · exact Or.inr (Or.inl (((tied_pair c).toLayer.only_height j
        ⟨le_of_not_gt low, le_of_not_gt high⟩).trans (center_height_left c)))

private theorem lower_cases (w : Fin W) : c.tied.lower w < c.lowerCut ∨
    c.tied.lower w = d.vertexHeight other ∨ c.upperCut < c.tied.lower w :=
  endpoint_cases c 0 (Or.inl c.lower_inside) (c.tied.start w)

private theorem upper_cases (w : Fin W) : c.tied.upper w < c.lowerCut ∨
    c.tied.upper w = d.vertexHeight other ∨ c.upperCut < c.tied.upper w :=
  endpoint_cases c 1 (Or.inr c.upper_inside) (c.tied.finish w)

private theorem before_state {y : ℝ} (low : c.lowerCut ≤ y) (high : y < d.vertexHeight other) (w : Fin W) :
    c.tied.crosses w y ↔ c.tied.crosses w c.lowerCut := by
  have lb := c.lower_bottom.trans (c.bottom_early.trans c.early_other)
  have ub := c.other_late.trans (c.late_top.trans c.top_upper)
  change (c.tied.lower w < y ∧ y < c.tied.upper w) ↔
    (c.tied.lower w < c.lowerCut ∧ c.lowerCut < c.tied.upper w)
  rcases lower_cases c w with hl | hl | hl <;> rcases upper_cases c w with hu | hu | hu <;>
    exact ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
      fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

private theorem after_state {y : ℝ} (low : d.vertexHeight other < y) (high : y ≤ c.upperCut) (w : Fin W) :
    c.tied.crosses w y ↔ c.tied.crosses w c.upperCut := by
  have lb := c.lower_bottom.trans (c.bottom_early.trans c.early_other)
  have ub := c.other_late.trans (c.late_top.trans c.top_upper)
  change (c.tied.lower w < y ∧ y < c.tied.upper w) ↔
    (c.tied.lower w < c.upperCut ∧ c.upperCut < c.tied.upper w)
  rcases lower_cases c w with hl | hl | hl <;> rcases upper_cases c w with hu | hu | hu <;>
    exact ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
      fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

theorem cut_before {y : ℝ} {ids : List (Fin W)} (cut : c.tied.OrderedCut c.lowerCut ids)
    (low : c.lowerCut ≤ y) (high : y < d.vertexHeight other) : c.tied.OrderedCut y ids := by
  refine cut.relocate_active fun w h hh => ?_
  rw [Set.uIcc_of_le low] at hh
  exact (before_state c hh.1 (hh.2.trans_lt high) w).symm

theorem cut_after {y : ℝ} {ids : List (Fin W)} (cut : c.tied.OrderedCut c.upperCut ids)
    (low : d.vertexHeight other < y) (high : y ≤ c.upperCut) : c.tied.OrderedCut y ids := by
  refine cut.relocate_active fun w h hh => ?_
  rw [Set.uIcc_of_ge high] at hh
  exact (after_state c (low.trans_le hh.1) hh.2 w).symm

theorem center_covered {w : Fin W} {y : ℝ} (low : c.lowerCut ≤ y) (high : y ≤ c.upperCut)
    (active : c.tied.crosses w y) : c.tied.covers w (d.vertexHeight other) := by
  have lb := c.lower_bottom.trans (c.bottom_early.trans c.early_other)
  have ub := c.other_late.trans (c.late_top.trans c.top_upper)
  change c.tied.lower w ≤ d.vertexHeight other ∧ d.vertexHeight other ≤ c.tied.upper w
  rcases lower_cases c w with hl | hl | hl <;> rcases upper_cases c w with hu | hu | hu <;>
    exact ⟨by linarith [active.1], by linarith [active.2]⟩

theorem cut_transport {h : ℝ} (valid : h ∈ Set.Icc s.bottom s.top) {y : ℝ} {ids : List (Fin W)} :
    (s.atHeight h valid).OrderedCut y ids ↔ c.tied.OrderedCut y ids :=
  (s.ordered_cut_iff valid).trans (s.ordered_cut_iff _).symm

theorem tied_lower (w : Fin W) : c.tied.lower w = d.lower w := s.lower_eq _ w

theorem tied_upper (w : Fin W) : c.tied.upper w = d.upper w := s.upper_eq _ w

theorem active_eq {h : ℝ} (valid : h ∈ Set.Icc s.bottom s.top) (w : Fin W) (y : ℝ) :
    (s.atHeight h valid).crosses w y ↔ c.tied.crosses w y := by
  simp only [Diagram.crosses, s.lower_eq valid, s.upper_eq valid, tied_lower c, tied_upper c]

/-- No point of a strand can pass across the scalar's vertical line. -/
theorem side_stable {w : Fin W} {y : ℝ} (band : y ∈ Set.Icc s.bottom s.top)
    (active : c.tied.crosses w y) :
    (c.tied.x w y < d.vertexX moved ↔ c.tied.x w (d.vertexHeight other) < d.vertexX moved) ∧
    (d.vertexX moved < c.tied.x w y ↔ d.vertexX moved < c.tied.x w (d.vertexHeight other)) := by
  let z := d.vertexHeight other
  have hz : z ∈ Set.Icc s.bottom s.top :=
    ⟨(c.bottom_early.trans c.early_other).le, (c.other_late.trans c.late_top).le⟩
  have center := center_covered c (c.lower_bottom.le.trans band.1) (band.2.trans c.top_upper.le) active
  have closed : c.tied.covers w y := ⟨active.1.le, active.2.le⟩
  have occupied (u : ℝ) (hu : u ∈ Set.uIcc y z) :
      c.tied.covers w u ∧ u ∈ Set.Icc s.bottom s.top :=
    ⟨⟨(le_min closed.1 center.1).trans hu.1, hu.2.trans (max_le closed.2 center.2)⟩,
      ⟨(le_min band.1 hz.1).trans hu.1, hu.2.trans (max_le band.2 hz.2)⟩⟩
  have clear (u : ℝ) (hu : u ∈ Set.uIcc y z) : c.tied.x w u ≠ d.vertexX moved := by
    have onWire := (occupied u hu).1
    have valid : d.covers w u := by
      simpa only [Diagram.covers, tied_lower c, tied_upper c] using onWire
    exact s.wire_clear w u (occupied u hu).2 valid
  have continuous : ContinuousOn (c.tied.x w) (Set.uIcc y z) :=
    (c.tied.wire w).continuous.mono (fun u hu => (occupied u hu).1)
  have noCross (hx : d.vertexX moved ∈ Set.uIcc (c.tied.x w y) (c.tied.x w z)) : False := by
    obtain ⟨u, hu, eq⟩ := intermediate_value_uIcc continuous hx
    exact clear u hu eq
  change (c.tied.x w y < d.vertexX moved ↔ c.tied.x w z < d.vertexX moved) ∧
    (d.vertexX moved < c.tied.x w y ↔ d.vertexX moved < c.tied.x w z)
  constructor <;> constructor <;> intro one <;> by_contra! two
  · exact noCross ⟨(min_le_left ..).trans one.le, two.trans (le_max_right ..)⟩
  · exact noCross ⟨(min_le_right ..).trans one.le, two.trans (le_max_left ..)⟩
  · exact noCross ⟨(min_le_right ..).trans two, one.le.trans (le_max_left ..)⟩
  · exact noCross ⟨(min_le_left ..).trans two, one.le.trans (le_max_right ..)⟩

end Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing
