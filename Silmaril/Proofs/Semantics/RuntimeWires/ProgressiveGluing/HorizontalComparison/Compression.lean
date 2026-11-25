module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Localize
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Geometry
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalComparison

open ProgressiveGraph ProgressiveGraph.OrderedKnots
open HorizontalPlacement (place_strict)

structure InteriorRange where
  left : ℝ
  right : ℝ
  left_inside : 0 < left
  order : left < right
  right_inside : right < 1

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' : ℕ}

def drawnXs (d : ProgressiveGraph.Diagram S V W .point) : Set ℝ :=
  Set.range d.vertexX ∪ ⋃ w, d.x w '' Set.Icc (d.lower w) (d.upper w)

theorem drawnXs_compact (d : ProgressiveGraph.Diagram S V W .point) : IsCompact (drawnXs d) := by
  refine (Set.finite_range d.vertexX).isCompact.union (isCompact_iUnion fun w => ?_)
  exact isCompact_Icc.image_of_continuousOn (d.wire w).continuous

theorem drawnXs_inside (d : ProgressiveGraph.Diagram S V W .point) :
    drawnXs d ⊆ Set.Ioo 0 1 := by
  intro x h
  rcases h with ⟨j, rfl⟩ | h
  · exact (d.vertex_inside j).1
  · obtain ⟨w, y, bounds, rfl⟩ := Set.mem_iUnion.mp h
    exact d.wire_inside w y bounds

theorem vertex_in_drawnXs (d : ProgressiveGraph.Diagram S V W .point) (j : Fin V) :
    d.vertexX j ∈ drawnXs d := .inl ⟨j, rfl⟩

theorem wire_in_drawnXs (d : ProgressiveGraph.Diagram S V W .point)
    (w : Fin W) {y : ℝ} (cover : d.covers w y) :
    d.x w y ∈ drawnXs d := .inr (Set.mem_iUnion.mpr ⟨w, y, cover, rfl⟩)

theorem common_range (d : ProgressiveGraph.Diagram S V W .point)
    (e : ProgressiveGraph.Diagram S V' W' .point) :
    ∃ span : InteriorRange, drawnXs d ⊆ Set.Icc span.left span.right ∧
      drawnXs e ⊆ Set.Icc span.left span.right := by
  let xs := insert (1 / 2 : ℝ) (drawnXs d ∪ drawnXs e)
  have hc : IsCompact xs := ((drawnXs_compact d).union (drawnXs_compact e)).insert _
  have ne : xs.Nonempty := ⟨1 / 2, Set.mem_insert _ _⟩
  have inside : xs ⊆ Set.Ioo 0 1 := by
    intro x mem
    rcases mem with rfl | mem
    · norm_num
    · exact mem.elim (fun h => drawnXs_inside d h) (fun h => drawnXs_inside e h)
  obtain ⟨a, ha⟩ := hc.exists_isLeast ne
  obtain ⟨b, hb⟩ := hc.exists_isGreatest ne
  let span : InteriorRange :=
    ⟨a / 2, (b + 1) / 2, by linarith [(inside ha.1).1],
      by linarith [(inside ha.1).1, (inside hb.1).2, hb.2 ha.1],
      by linarith [(inside hb.1).2]⟩
  have bound {x : ℝ} (h : x ∈ xs) : x ∈ Set.Icc span.left span.right :=
    ⟨by change a / 2 ≤ x; linarith [(inside ha.1).1, ha.2 h],
      by change x ≤ (b + 1) / 2; linarith [(inside hb.1).2, hb.2 h]⟩
  exact ⟨span, fun _ h => bound (.inr (.inl h)), fun _ h => bound (.inr (.inr h))⟩

/-- Compactness in height supplies finite outer bounds for the two
reference fibres. At exterior heights the original map is the identity. -/
theorem outer_bounds (f : CapHomeomorph) (a b : ℝ) :
    ∃ l r : ℝ, l < a ∧ b < r ∧
      (∀ y, l < fibre f y a) ∧ (∀ y, fibre f y b < r) := by
  have comp (x : ℝ) : IsCompact ((fun y => fibre f y x) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image ((f.plane.continuous.comp (continuous_const.prodMk continuous_id)).fst)
  obtain ⟨l, hl⟩ := (comp a).bddBelow
  obtain ⟨r, hr⟩ := (comp b).bddAbove
  refine ⟨min a l - 1, max b r + 1, by linarith [min_le_left a l],
    by linarith [le_max_left b r], ?_, ?_⟩
  · intro y
    by_cases h : y ∈ Set.Icc (0 : ℝ) 1
    · exact (by linarith [min_le_right a l] : min a l - 1 < l).trans_le (hl ⟨y, h, rfl⟩)
    · have outside : y < 0 ∨ 1 < y := by simpa only [Set.mem_Icc, not_and_or, not_le] using h
      rw [fibre_fixed f (outside.imp le_of_lt le_of_lt)]
      linarith [min_le_left a l]
  · intro y
    by_cases h : y ∈ Set.Icc (0 : ℝ) 1
    · exact (hr ⟨y, h, rfl⟩).trans_lt (by linarith [le_max_right b r])
    · have outside : y < 0 ∨ 1 < y := by simpa only [Set.mem_Icc, not_and_or, not_le] using h
      rw [fibre_fixed f (outside.imp le_of_lt le_of_lt)]
      linarith [le_max_left b r]

structure Compression (f : CapHomeomorph) (s : ActiveStrip) (span : InteriorRange) where
  outerLeft : ℝ
  outerRight : ℝ
  left_order : outerLeft < span.left
  right_order : span.right < outerRight
  left_bound : ∀ y, outerLeft < fibre f y span.left
  right_bound : ∀ y, fibre f y span.right < outerRight

def compression (f : CapHomeomorph) (s : ActiveStrip) (span : InteriorRange) :
    Compression f s span :=
  let h := outer_bounds f span.left span.right
  let bounds := Classical.choose_spec (Classical.choose_spec h)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2⟩

namespace Compression

variable {f : CapHomeomorph} {s : ActiveStrip} {span : InteriorRange} (c : Compression f s span)

def fromKnots : Fin 4 → ℝ := knots c.outerLeft span.left span.right c.outerRight

def toKnots : Fin 4 → ℝ :=
  knots ((s.place 0 + s.place span.left) / 2) (s.place span.left)
    (s.place span.right) ((s.place span.right + s.place 1) / 2)

theorem from_strict : StrictMono c.fromKnots :=
  knots_strict c.left_order span.order c.right_order

theorem to_strict : StrictMono (toKnots (s := s) (span := span)) :=
  knots_strict (by linarith [place_strict s span.left_inside])
    (place_strict s span.order) (by linarith [place_strict s span.right_inside])

def chart : ℝ ≃ₜ ℝ := OrderedKnots.homeomorph c.from_strict (to_strict (s := s) (span := span))

theorem chart_apply (x : ℝ) : c.chart x = transfer c.fromKnots (toKnots (s := s) (span := span)) x :=
  homeomorph_apply c.from_strict (to_strict (s := s) (span := span)) x

theorem chart_strict : StrictMono c.chart := by
  intro a b h
  rw [c.chart_apply, c.chart_apply]
  exact transfer_strictMono c.from_strict (to_strict (s := s) (span := span)) h

theorem chart_middle {x : ℝ} (h : x ∈ Set.Icc span.left span.right) : c.chart x = s.place x := by
  rw [c.chart_apply, transfer_segment c.from_strict (1 : Fin 3) h]
  change s.place span.left + (s.place span.right - s.place span.left) *
    ((x - span.left) / (span.right - span.left)) = _
  have hn := ne_of_gt (sub_pos.mpr span.order)
  cases s <;> simp only [ActiveStrip.place] <;> field_simp <;> ring

theorem chart_lower_wall : s.place 0 < c.chart c.outerLeft := by
  rw [c.chart_apply]
  have h := transfer_knot (b := toKnots (s := s) (span := span)) c.from_strict 0
  change transfer c.fromKnots (toKnots (s := s) (span := span)) c.outerLeft =
    (s.place 0 + s.place span.left) / 2 at h
  rw [h]
  linarith [place_strict s span.left_inside]

theorem chart_upper_wall : c.chart c.outerRight < s.place 1 := by
  rw [c.chart_apply]
  have h := transfer_knot (b := toKnots (s := s) (span := span)) c.from_strict 3
  change transfer c.fromKnots (toKnots (s := s) (span := span)) c.outerRight =
    (s.place span.right + s.place 1) / 2 at h
  rw [h]
  linarith [place_strict s span.right_inside]

def window : Window (conjugate f c.chart) where
  wallLeft := s.place 0
  cutLeft := s.place span.left
  cutRight := s.place span.right
  wallRight := s.place 1
  left_inside := place_strict s span.left_inside
  cut_order := place_strict s span.order
  right_inside := place_strict s span.right_inside
  left_image y := by
    rw [conjugate_fibre, ← c.chart_middle ⟨le_rfl, span.order.le⟩, c.chart.symm_apply_apply]
    exact c.chart_lower_wall.trans (c.chart_strict (c.left_bound y))
  right_image y := by
    rw [conjugate_fibre, ← c.chart_middle ⟨span.order.le, le_rfl⟩, c.chart.symm_apply_apply]
    exact (c.chart_strict (c.right_bound y)).trans c.chart_upper_wall

def ambient : CapHomeomorph := c.window.localize

theorem ambient_active {x y : ℝ} (before : x ∈ Set.Icc span.left span.right)
    (after : fibre f y x ∈ Set.Icc span.left span.right) :
    c.ambient.plane (s.place x, y) = (s.place (fibre f y x), f.height y) := by
  have mid : s.place x ∈ Set.Icc c.window.cutLeft c.window.cutRight :=
    ⟨(place_strict s).monotone before.1, (place_strict s).monotone before.2⟩
  change c.window.localizedPlane (s.place x, y) = _
  rw [c.window.localized_middle mid, plane_eq, conjugate_fibre]
  have inv : c.chart.symm (s.place x) = x := by rw [← c.chart_middle before, c.chart.symm_apply_apply]
  rw [inv, c.chart_middle after]
  rfl

theorem ambient_idle {x : ℝ} (h : x ∈ Set.Ioo 0 1) (y : ℝ) :
    c.ambient.plane (s.opposite.place x, y) = (s.opposite.place x, f.height y) := by
  apply c.window.localized_exterior
  change s.opposite.place x ≤ s.place 0 ∨ s.place 1 ≤ s.opposite.place x
  cases s
  · right
    simp only [ActiveStrip.opposite, ActiveStrip.place]
    linarith [h.1]
  · left
    simp only [ActiveStrip.opposite, ActiveStrip.place]
    linarith [h.2]

end Compression
end Silmaril.RuntimeWires.Proofs.HorizontalComparison
