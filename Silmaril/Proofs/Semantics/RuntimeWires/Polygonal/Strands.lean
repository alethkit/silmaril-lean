module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Defs
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.Polygonal

open Silmaril.RuntimeWires.Polygonal

theorem interpolate_mono {a b x y t : ℝ} (ha : a ≤ x) (hb : b ≤ y) (ht : t ∈ Set.Icc 0 1) :
    interpolate a b t ≤ interpolate x y t :=
  add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hb ht.1)

theorem interpolate_strict {a b x y t : ℝ} (ha : a < x) (hb : b < y) (ht : t ∈ Set.Icc 0 1) :
    interpolate a b t < interpolate x y t := by
  obtain rfl | hpos := eq_or_lt_of_le ht.1
  · simpa [interpolate] using ha
  · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr ht.2))
      (mul_lt_mul_of_pos_left hb hpos)

theorem interpolate_self (x t : ℝ) : interpolate x x t = x := by
  unfold interpolate
  ring

private theorem linear_height (a b t : ℝ) : interpolate a b t = a + t * (b - a) := by
  unfold interpolate
  ring

theorem height_strict {slab : Slab} (s : Strand slab) :
    StrictMono (fun t => (s.point t).2) := by
  intro t u h
  change interpolate slab.lower slab.upper t < interpolate slab.lower slab.upper u
  rw [linear_height, linear_height]
  exact add_lt_add_right (mul_lt_mul_of_pos_right h (sub_pos.mpr slab.increasing)) _

theorem trace_height {slab : Slab} {s : Strand slab} {p : Point} (h : p ∈ s.trace) :
    p.2 ∈ Set.Icc slab.lower slab.upper := by
  obtain ⟨t, ht, rfl⟩ := h
  have lo := (height_strict s).monotone ht.1
  have hi := (height_strict s).monotone ht.2
  exact ⟨by simpa [Strand.point, interpolate] using lo,
    by simpa [Strand.point, interpolate] using hi⟩

theorem lower_cap {slab : Slab} {s : Strand slab} {p : Point} (hp : p ∈ s.trace)
    (h : p.2 = slab.lower) : p = (s.start, slab.lower) := by
  obtain ⟨t, _, rfl⟩ := hp
  have e : t = 0 := (height_strict s).injective (h.trans (by simp [Strand.point, interpolate]))
  simp [e, Strand.point, interpolate]

theorem upper_cap {slab : Slab} {s : Strand slab} {p : Point} (hp : p ∈ s.trace)
    (h : p.2 = slab.upper) : p = (s.finish, slab.upper) := by
  obtain ⟨t, _, rfl⟩ := hp
  have e : t = 1 := (height_strict s).injective (h.trans (by simp [Strand.point, interpolate]))
  simp [e, Strand.point, interpolate]

theorem trace_horizontal {slab : Slab} {s : Strand slab} {p : Point}
    {left right : ℝ} (hp : p ∈ s.trace) (hstart : s.start ∈ Set.Ioo left right)
    (hfinish : s.finish ∈ Set.Ioo left right) : p.1 ∈ Set.Ioo left right := by
  obtain ⟨t, ht, rfl⟩ := hp
  have lo := interpolate_strict hstart.1 hfinish.1 ht
  have hi := interpolate_strict hstart.2 hfinish.2 ht
  rw [interpolate_self] at lo hi
  exact ⟨lo, hi⟩

theorem trace_disjoint {slab : Slab} {s r : Strand slab} (hs : s.start < r.start)
    (hf : s.finish < r.finish) : Disjoint s.trace r.trace := by
  rw [Set.disjoint_left]
  intro p hp hq
  obtain ⟨t, ht, rfl⟩ := hp
  obtain ⟨u, hu, e⟩ := hq
  have sameHeight := congrArg Prod.snd e
  change (s.point u).2 = (s.point t).2 at sameHeight
  have time : u = t := (height_strict s).injective sameHeight
  subst u
  exact (ne_of_lt (interpolate_strict hs hf ht)) (congrArg Prod.fst e).symm

universe u

variable {O : Type u} {A : List O}

theorem order_coordinates (p : Frontier A) : StrictMono p.coordinate := by
  intro i j hij
  exact (List.pairwise_iff_get.mp p.ordered) _ _ hij

theorem connector_disjoint (slab : Slab) (p q : Frontier A) {i j : Fin A.length} (h : i ≠ j) :
    Disjoint (connector slab p q i).trace (connector slab p q j).trace := by
  rcases lt_or_gt_of_ne h with hij | hji
  · exact trace_disjoint (order_coordinates p hij) (order_coordinates q hij)
  · exact (trace_disjoint (s := connector slab p q j) (r := connector slab p q i)
      (order_coordinates p hji) (order_coordinates q hji)).symm

/-- All strands in a connector cross a given level at the same parameter. -/
theorem level_parameter (slab : Slab) {y : ℝ} (hy : y ∈ Set.Icc slab.lower slab.upper) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, interpolate slab.lower slab.upper t = y := by
  have positive := sub_pos.mpr slab.increasing
  let t := (y - slab.lower) / (slab.upper - slab.lower)
  refine ⟨t, ⟨div_nonneg (sub_nonneg.mpr hy.1) positive.le,
    (div_le_one positive).mpr (sub_le_sub_right hy.2 _)⟩, ?_⟩
  rw [linear_height, div_mul_cancel₀ _ positive.ne']
  ring

end Silmaril.RuntimeWires.Proofs.Polygonal
