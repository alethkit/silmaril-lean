module

public import Silmaril.Semantics.RuntimeWires.PolygonalCuts.Defs
import Silmaril.Semantics.RuntimeWires.Polygonal.Thms
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalCuts

open Silmaril.RuntimeWires.Polygonal

variable {slab : Slab} (c : slab.Cut)

private theorem height_at_cut : interpolate slab.lower slab.upper c.parameter = c.height := by
  calc
    interpolate slab.lower slab.upper c.parameter =
        slab.lower + c.parameter * (slab.upper - slab.lower) := by
          unfold interpolate
          ring
    _ = c.height := by
      rw [Slab.Cut.parameter, div_mul_cancel₀ _ (sub_pos.mpr slab.increasing).ne']
      ring

private theorem point_at_cut (s : Strand slab) : s.point c.parameter = (c.coordinate s, c.height) :=
  Prod.ext rfl (height_at_cut c)

private theorem lower_point (s : Strand slab) (u : ℝ) :
    (c.lowerStrand s).point u = s.point (c.parameter * u) := by
  apply Prod.ext
  · change interpolate s.start (interpolate s.start s.finish c.parameter) u = _
    unfold Strand.point interpolate
    ring
  · change interpolate slab.lower c.height u = _
    rw [← height_at_cut c]
    unfold Strand.point interpolate
    ring

private theorem upper_point (s : Strand slab) (u : ℝ) :
    (c.upperStrand s).point u = s.point (c.parameter + (1 - c.parameter) * u) := by
  apply Prod.ext
  · change interpolate (interpolate s.start s.finish c.parameter) s.finish u = _
    unfold Strand.point interpolate
    ring
  · change interpolate c.height slab.upper u = _
    rw [← height_at_cut c]
    unfold Strand.point interpolate
    ring

theorem lower_trace (s : Strand slab) :
    (c.lowerStrand s).trace = s.trace ∩ {z | z.2 ≤ c.height} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have low : 0 ≤ c.parameter * u := mul_nonneg c.parameter_pos.le hu.1
    have high : c.parameter * u ≤ c.parameter := mul_le_of_le_one_right c.parameter_pos.le hu.2
    rw [lower_point]
    exact ⟨⟨_, ⟨low, high.trans c.parameter_lt_one.le⟩, rfl⟩,
      (s.strictHeight.monotone high).trans_eq (height_at_cut c)⟩
  · rintro ⟨⟨t, ht, rfl⟩, h⟩
    have high : t ≤ c.parameter := s.strictHeight.le_iff_le.mp (h.trans_eq (height_at_cut c).symm)
    have hu : t / c.parameter ∈ Set.Icc 0 1 :=
      ⟨div_nonneg ht.1 c.parameter_pos.le, (div_le_one c.parameter_pos).mpr high⟩
    refine ⟨t / c.parameter, hu, ?_⟩
    rw [lower_point, mul_comm, div_mul_cancel₀ _ c.parameter_pos.ne']

theorem upper_trace (s : Strand slab) :
    (c.upperStrand s).trace = s.trace ∩ {z | c.height ≤ z.2} := by
  have positive : 0 < 1 - c.parameter := sub_pos.mpr c.parameter_lt_one
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have low : c.parameter ≤ c.parameter + (1 - c.parameter) * u :=
      le_add_of_nonneg_right (mul_nonneg positive.le hu.1)
    have high : c.parameter + (1 - c.parameter) * u ≤ 1 := calc
      _ ≤ c.parameter + (1 - c.parameter) :=
        add_le_add_right (mul_le_of_le_one_right positive.le hu.2) _
      _ = 1 := add_sub_cancel c.parameter 1
    rw [upper_point]
    exact ⟨⟨_, ⟨c.parameter_pos.le.trans low, high⟩, rfl⟩,
      (height_at_cut c).symm.trans_le (s.strictHeight.monotone low)⟩
  · rintro ⟨⟨t, ht, rfl⟩, h⟩
    have low : c.parameter ≤ t := s.strictHeight.le_iff_le.mp ((height_at_cut c).trans_le h)
    have hu : (t - c.parameter) / (1 - c.parameter) ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (sub_nonneg.mpr low) positive.le,
        (div_le_one positive).mpr (sub_le_sub_right ht.2 _)⟩
    refine ⟨(t - c.parameter) / (1 - c.parameter), hu, ?_⟩
    rw [upper_point, mul_comm (1 - c.parameter), div_mul_cancel₀ _ positive.ne', add_sub_cancel]

theorem join_trace (s : Strand slab) : (c.lowerStrand s).trace ∪ (c.upperStrand s).trace = s.trace := by
  rw [lower_trace, upper_trace]
  ext z
  exact ⟨fun h => h.elim And.left And.left, fun h =>
    (le_total z.2 c.height).elim (fun hz => Or.inl ⟨h, hz⟩) (fun hz => Or.inr ⟨h, hz⟩)⟩

theorem contact_at_cut (s : Strand slab) :
    (c.lowerStrand s).trace ∩ (c.upperStrand s).trace = {(c.coordinate s, c.height)} := by
  rw [lower_trace, upper_trace]
  ext z
  constructor
  · rintro ⟨⟨⟨t, _, rfl⟩, lo⟩, _, hi⟩
    have sameHeight : (s.point t).2 = (s.point c.parameter).2 :=
      (le_antisymm lo hi).trans (height_at_cut c).symm
    rw [s.strictHeight.injective sameHeight, point_at_cut]
    exact Set.mem_singleton _
  · rintro rfl
    have h : (c.coordinate s, c.height) ∈ s.trace :=
      ⟨c.parameter, ⟨c.parameter_pos.le, c.parameter_lt_one.le⟩, point_at_cut c s⟩
    change ((c.coordinate s, c.height) ∈ s.trace ∧ c.height ≤ c.height) ∧
      ((c.coordinate s, c.height) ∈ s.trace ∧ c.height ≤ c.height)
    exact ⟨⟨h, le_rfl⟩, h, le_rfl⟩

variable {O : Type*} {A : List O}

theorem frontier_coordinate (p q : Frontier A) (i : Fin A.length) :
    (c.frontier p q).coordinate i = c.coordinate (connector slab p q i) := by
  simp [Slab.Cut.frontier, Frontier.coordinate, Frontier.ofCoordinates]
  rfl

theorem lower_connector (p q : Frontier A) (i : Fin A.length) :
    connector c.lower p (c.frontier p q) i = c.lowerStrand (connector slab p q i) := by
  change Strand.mk _ _ = Strand.mk _ _
  rw [frontier_coordinate]
  rfl

theorem upper_connector (p q : Frontier A) (i : Fin A.length) :
    connector c.upper (c.frontier p q) q i = c.upperStrand (connector slab p q i) := by
  change Strand.mk _ _ = Strand.mk _ _
  rw [frontier_coordinate]
  rfl

private theorem contains_connector {slab' : Slab} (p q : Frontier A) (z : Point) :
    (Part.connector slab' p q).Contains z ↔ ∃ i, z ∈ (connector slab' p q i).trace := by
  constructor
  · rintro ⟨region, hr, hz⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨i, hz⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩

theorem connector_join (p q : Frontier A) (z : Point) :
    ((Part.connector c.lower p (c.frontier p q)).Contains z ∨
      (Part.connector c.upper (c.frontier p q) q).Contains z) ↔
    (Part.connector slab p q).Contains z := by
  simp only [contains_connector, lower_connector, upper_connector, ← exists_or,
    ← Set.mem_union, join_trace]

theorem connector_contact (p q : Frontier A) (z : Point) :
    ((Part.connector c.lower p (c.frontier p q)).Contains z ∧
      (Part.connector c.upper (c.frontier p q) q).Contains z) ↔
    ∃ i : Fin A.length, z = ((c.frontier p q).coordinate i, c.height) := by
  simp only [contains_connector, lower_connector, upper_connector, frontier_coordinate]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [lower_trace] at hi
    rw [upper_trace] at hj
    have e : i = j := by
      by_contra h
      exact Set.disjoint_left.mp (connector_trace_disjoint slab p q h) hi.1 hj.1
    subst j
    refine ⟨i, ?_⟩
    have hz : z ∈ (c.lowerStrand (connector slab p q i)).trace ∩
        (c.upperStrand (connector slab p q i)).trace := by
      rw [lower_trace, upper_trace]
      exact ⟨hi, hj⟩
    rw [contact_at_cut] at hz
    exact hz
  · rintro ⟨i, rfl⟩
    have hz : (c.coordinate (connector slab p q i), c.height) ∈
        (c.lowerStrand (connector slab p q i)).trace ∩
          (c.upperStrand (connector slab p q i)).trace := by
      rw [contact_at_cut]
      exact Set.mem_singleton _
    exact ⟨⟨i, hz.1⟩, ⟨i, hz.2⟩⟩

end Silmaril.RuntimeWires.Proofs.PolygonalCuts
