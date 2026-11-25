module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialWires
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Drawing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (height_left height_right x_left x_right lower_inside upper_inside unscale)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

theorem covered_lower (w : Fin A) {y : ℝ} (hy : y ≤ 1 / 2) :
    y ∈ Set.Icc (wireLo (fromLower w : WireId lower upper)) (wireHi m (fromLower w)) ↔
      lower.covers w (slabHeight 0 y) := by
  obtain ⟨lo, hi⟩ := bounds_fromLower m w
  change wireLo (fromLower w : WireId lower upper) ≤ y ∧ y ≤ wireHi m (fromLower w) ↔
    lower.lower w ≤ slabHeight 0 y ∧ slabHeight 0 y ≤ lower.upper w
  rw [lo]
  constructor
  · intro h
    have last := le_min h.2 hy
    rw [hi] at last
    unfold halfHeight slabHeight at *
    exact ⟨by linarith [h.1], by linarith⟩
  · intro h
    have last : y ≤ min (wireHi m (fromLower w)) (1 / 2) := by
      rw [hi]
      unfold halfHeight slabHeight at *
      linarith [h.2]
    unfold halfHeight slabHeight at *
    exact ⟨by linarith [h.1], last.trans (min_le_left ..)⟩

theorem active_lower (w : Fin A) {y : ℝ} (hy : y < 1 / 2) :
    y ∈ Set.Ioo (wireLo (fromLower w : WireId lower upper)) (wireHi m (fromLower w)) ↔
      lower.crosses w (slabHeight 0 y) := by
  obtain ⟨lo, hi⟩ := bounds_fromLower m w
  change wireLo (fromLower w : WireId lower upper) < y ∧ y < wireHi m (fromLower w) ↔
    lower.lower w < slabHeight 0 y ∧ slabHeight 0 y < lower.upper w
  rw [lo]
  constructor
  · intro h
    have last := lt_min h.2 hy
    rw [hi] at last
    unfold halfHeight slabHeight at *
    exact ⟨by linarith [h.1], by linarith⟩
  · intro h
    have last : y < min (wireHi m (fromLower w)) (1 / 2) := by
      rw [hi]
      unfold halfHeight slabHeight at *
      linarith [h.2]
    unfold halfHeight slabHeight at *
    exact ⟨by linarith [h.1], last.trans_le (min_le_left ..)⟩

theorem covered_upper (w : Fin B) {y : ℝ} (hy : 1 / 2 ≤ y) :
    y ∈ Set.Icc (wireLo (m.fromUpper w)) (wireHi m (m.fromUpper w)) ↔
      upper.covers w (slabHeight 1 y) := by
  obtain ⟨lo, hi⟩ := bounds_fromUpper m w
  change wireLo (m.fromUpper w) ≤ y ∧ y ≤ wireHi m (m.fromUpper w) ↔
    upper.lower w ≤ slabHeight 1 y ∧ slabHeight 1 y ≤ upper.upper w
  rw [hi]
  constructor
  · intro h
    have first := max_le h.1 hy
    rw [lo] at first
    unfold halfHeight slabHeight at *
    exact ⟨by linarith, by linarith [h.2]⟩
  · intro h
    have first : max (wireLo (m.fromUpper w)) (1 / 2) ≤ y := by
      rw [lo]
      unfold halfHeight slabHeight at *
      linarith [h.1]
    unfold halfHeight slabHeight at *
    exact ⟨(le_max_left ..).trans first, by linarith [h.2]⟩

theorem active_upper (w : Fin B) {y : ℝ} (hy : 1 / 2 < y) :
    y ∈ Set.Ioo (wireLo (m.fromUpper w)) (wireHi m (m.fromUpper w)) ↔
      upper.crosses w (slabHeight 1 y) := by
  obtain ⟨lo, hi⟩ := bounds_fromUpper m w
  change wireLo (m.fromUpper w) < y ∧ y < wireHi m (m.fromUpper w) ↔
    upper.lower w < slabHeight 1 y ∧ slabHeight 1 y < upper.upper w
  rw [hi]
  constructor
  · intro h
    have first := max_lt h.1 hy
    rw [lo] at first
    unfold halfHeight slabHeight at *
    exact ⟨by linarith, by linarith [h.2]⟩
  · intro h
    have first : max (wireLo (m.fromUpper w)) (1 / 2) < y := by
      rw [lo]
      unfold halfHeight slabHeight at *
      linarith [h.1]
    unfold halfHeight slabHeight at *
    exact ⟨(le_max_left ..).trans_lt first, by linarith [h.2]⟩

theorem lower_present {z : WireId lower upper} {y : ℝ}
    (hy : y ≤ 1 / 2) (low : wireLo z ≤ y) : ∃ w, fromLower w = z := by
  rcases z with z | (z | z)
  · exact ⟨z.val, lower_exists.mpr rfl⟩
  · exact ⟨z.val, lower_exists.mpr rfl⟩
  · exact ((lo_right_gt (lower := lower) z).not_ge (low.trans hy)).elim

theorem upper_present {z : WireId lower upper} {y : ℝ}
    (hy : 1 / 2 ≤ y) (high : y ≤ wireHi m z) : ∃ w, m.fromUpper w = z := by
  rcases z with z | (z | z)
  · exact ((hi_left_lt m z).not_ge (hy.trans high)).elim
  · exact ⟨(m.contact z).val, (upper_exists m).mpr rfl⟩
  · exact ⟨z.val, (upper_exists m).mpr rfl⟩

theorem shared_present {z : WireId lower upper}
    (h : (1 / 2 : ℝ) ∈ Set.Icc (wireLo z) (wireHi m z)) :
    ∃ w : Contact lower, z = .inr (.inl w) := by
  rcases z with z | (z | z)
  · exact ((hi_left_lt m z).not_ge h.2).elim
  · exact ⟨z, rfl⟩
  · exact ((lo_right_gt (lower := lower) z).not_ge h.1).elim

theorem wire_inside (z : WireId lower upper) (y : ℝ)
    (cover : y ∈ Set.Icc (wireLo z) (wireHi m z)) : (jointWire m z).x y ∈ Set.Ioo 0 1 := by
  rcases le_total y (1 / 2 : ℝ) with hy | hy
  · obtain ⟨w, rfl⟩ := lower_present hy cover.1
    rw [x_fromLower m w hy]
    exact lower.wire_inside w _ ((covered_lower m w hy).mp cover)
  · obtain ⟨w, rfl⟩ := upper_present m hy cover.2
    rw [x_fromUpper m w hy]
    exact upper.wire_inside w _ ((covered_upper m w hy).mp cover)

theorem separated {w z : WireId lower upper} (different : w ≠ z) {y : ℝ}
    (inside : y ∈ Set.Ioo (wireLo w) (wireHi m w))
    (cover : y ∈ Set.Icc (wireLo z) (wireHi m z)) :
    (jointWire m w).x y ≠ (jointWire m z).x y := by
  rcases lt_trichotomy y (1 / 2 : ℝ) with hy | rfl | hy
  · obtain ⟨a, rfl⟩ := lower_present hy.le inside.1.le
    obtain ⟨b, rfl⟩ := lower_present hy.le cover.1
    rw [x_fromLower m a hy.le, x_fromLower m b hy.le]
    exact lower.separated (fun eq => different (congrArg fromLower eq))
      ((active_lower m a hy).mp inside) ((covered_lower m b hy.le).mp cover)
  · obtain ⟨a, rfl⟩ := shared_present m (Set.Ioo_subset_Icc_self inside)
    obtain ⟨b, rfl⟩ := shared_present m cover
    rw [← fromLower_shared (upper := upper) a, ← fromLower_shared (upper := upper) b,
      x_fromLower m a.val le_rfl, x_fromLower m b.val le_rfl]
    have ne : a.val ≠ b.val := fun eq =>
      different (congrArg (fun c : Contact lower => (.inr (.inl c) : WireId lower upper)) (Subtype.ext eq))
    simpa only [Diagram.x, show slabHeight 0 (1 / 2) = 1 by norm_num [slabHeight]] using
      lower.output_boundary_separated ne a.property b.property
  · obtain ⟨a, rfl⟩ := upper_present m hy.le inside.2.le
    obtain ⟨b, rfl⟩ := upper_present m hy.le cover.2
    rw [x_fromUpper m a hy.le, x_fromUpper m b hy.le]
    exact upper.separated (fun eq => different (congrArg m.fromUpper eq))
      ((active_upper m a hy).mp inside) ((covered_upper m b hy.le).mp cover)

theorem order_across {w z : WireId lower upper} {a b : ℝ}
    (wa : a ∈ Set.Ioo (wireLo w) (wireHi m w)) (za : a ∈ Set.Ioo (wireLo z) (wireHi m z))
    (wb : b ∈ Set.Ioo (wireLo w) (wireHi m w)) (zb : b ∈ Set.Ioo (wireLo z) (wireHi m z))
    (ordered : (jointWire m w).x a < (jointWire m z).x a) :
    (jointWire m w).x b < (jointWire m z).x b :=
  Proofs.ProgressiveGluing.transport_wire_order (jointWire m) (separated m) wa za wb zb ordered

theorem avoids_vertex (z : WireId lower upper) (j : Fin (L + R))
    (h : gluedHeight lower upper j ∈ Set.Ioo (wireLo z) (wireHi m z)) :
    (jointWire m z).x (gluedHeight lower upper j) ≠ gluedVertexX lower upper j := by
  induction j using Fin.addCases with
  | left v =>
    rw [height_left] at h
    have hy := (lower_inside (lower := lower) v).2
    obtain ⟨w, rfl⟩ := lower_present hy.le h.1.le
    have h' := (active_lower m w hy).mp h
    rw [unscale] at h'
    rw [height_left, x_left, x_fromLower m w hy.le, unscale]
    exact lower.avoids_vertex w v h'
  | right v =>
    rw [height_right] at h
    have hy := (upper_inside (upper := upper) v).1
    obtain ⟨w, rfl⟩ := upper_present m hy.le h.2.le
    have h' := (active_upper m w hy).mp h
    rw [unscale] at h'
    rw [height_right, x_right, x_fromUpper m w hy.le, unscale]
    exact upper.avoids_vertex w v h'

end Silmaril.RuntimeWires.Proofs.PartialGluing
