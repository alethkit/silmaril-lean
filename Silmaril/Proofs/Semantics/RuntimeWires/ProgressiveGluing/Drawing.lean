module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Ports
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

noncomputable def jointLower (lower : Diagram S L W .point) (upper : Diagram S R W .point) (w : Fin W) : ℝ :=
  endpointHeight (gluedHeight lower upper) 0 (gluedStart (R := R) lower w)

noncomputable def jointUpper (lower : Diagram S L W .point) (upper : Diagram S R W .point) (w : Fin W) : ℝ :=
  endpointHeight (gluedHeight lower upper) 1 (gluedFinish (L := L) upper w)

include m in
theorem left_covered {w : Fin W} {y : ℝ} (atLeft : y ≤ 1 / 2) (hw : jointLower lower upper w ≤ y) :
    lower.covers w (slabHeight 0 y) := by
  change lower.lower w ≤ slabHeight 0 y ∧ slabHeight 0 y ≤ lower.upper w
  rw [lower_cap_height m w]
  change endpointHeight (gluedHeight lower upper) 0 (gluedStart lower w) ≤ y at hw
  rw [low_bound] at hw
  unfold halfHeight at hw
  unfold slabHeight
  exact ⟨by linarith, by linarith⟩

include m in
theorem right_covered {w : Fin W} {y : ℝ} (atRight : 1 / 2 ≤ y) (hw : y ≤ jointUpper lower upper w) :
    upper.covers w (slabHeight 1 y) := by
  change upper.lower w ≤ slabHeight 1 y ∧ slabHeight 1 y ≤ upper.upper w
  rw [upper_cap_height m w]
  change y ≤ endpointHeight (gluedHeight lower upper) 1 (gluedFinish upper w) at hw
  rw [high_bound] at hw
  unfold halfHeight at hw
  unfold slabHeight
  exact ⟨by linarith, by linarith⟩

include m in
theorem left_active {w : Fin W} {y : ℝ} (atLeft : y < 1 / 2) (hw : jointLower lower upper w < y) :
    lower.crosses w (slabHeight 0 y) := by
  change lower.lower w < slabHeight 0 y ∧ slabHeight 0 y < lower.upper w
  rw [lower_cap_height m w]
  change endpointHeight (gluedHeight lower upper) 0 (gluedStart lower w) < y at hw
  rw [low_bound] at hw
  unfold halfHeight at hw
  unfold slabHeight
  exact ⟨by linarith, by linarith⟩

include m in
theorem right_active {w : Fin W} {y : ℝ} (atRight : 1 / 2 < y) (hw : y < jointUpper lower upper w) :
    upper.crosses w (slabHeight 1 y) := by
  change upper.lower w < slabHeight 1 y ∧ slabHeight 1 y < upper.upper w
  rw [upper_cap_height m w]
  change y < endpointHeight (gluedHeight lower upper) 1 (gluedFinish upper w) at hw
  rw [high_bound] at hw
  unfold halfHeight at hw
  unfold slabHeight
  exact ⟨by linarith, by linarith⟩

include m in
theorem join_inside (w : Fin W) : (1 / 2 : ℝ) ∈ Set.Ioo (jointLower lower upper w) (jointUpper lower upper w) := by
  change endpointHeight (gluedHeight lower upper) 0 (gluedStart lower w) < (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) < endpointHeight (gluedHeight lower upper) 1 (gluedFinish upper w)
  rw [low_bound, high_bound]
  exact ⟨below_join m w, above_join m w⟩

theorem separated_wires {w z : Fin W} (different : w ≠ z) {y : ℝ}
    (a : y ∈ Set.Ioo (jointLower lower upper w) (jointUpper lower upper w))
    (b : y ∈ Set.Icc (jointLower lower upper z) (jointUpper lower upper z)) :
    (gluedWire m w).x y ≠ (gluedWire m z).x y := by
  rcases lt_trichotomy y (1 / 2 : ℝ) with lt | eq | gt
  · rw [wire_left m w lt.le, wire_left m z lt.le]
    exact lower.separated different (left_active m lt a.1) (left_covered m lt.le b.1)
  · subst y
    rw [wire_left m w le_rfl, wire_left m z le_rfl]
    simpa only [Diagram.x, show slabHeight 0 (1 / 2) = 1 by norm_num [slabHeight]] using
      lower.output_boundary_separated different (m.lower_cap w) (m.lower_cap z)
  · rw [wire_right m w gt.le, wire_right m z gt.le]
    exact upper.separated different (right_active m gt a.2) (right_covered m gt.le b.2)

theorem wire_inside (w : Fin W) (y : ℝ)
    (h : y ∈ Set.Icc (jointLower lower upper w) (jointUpper lower upper w)) :
    (gluedWire m w).x y ∈ Set.Ioo 0 1 := by
  rcases le_total y (1 / 2 : ℝ) with lo | hi
  · rw [wire_left m w lo]
    exact lower.wire_inside w _ (left_covered m lo h.1)
  · rw [wire_right m w hi]
    exact upper.wire_inside w _ (right_covered m hi h.2)

theorem vertex_inside (j : Fin (L + R)) :
    gluedVertexX lower upper j ∈ Set.Ioo 0 1 ∧ gluedHeight lower upper j ∈ Set.Ioo 0 1 := by
  induction j using Fin.addCases with
  | left v =>
    rw [x_left, height_left]
    have h := lower_inside (lower := lower) v
    exact ⟨(lower.vertex_inside v).1, h.1, h.2.trans (by norm_num)⟩
  | right v =>
    rw [x_right, height_right]
    have h := upper_inside (upper := upper) v
    exact ⟨(upper.vertex_inside v).1, (by norm_num : (0 : ℝ) < 1 / 2).trans h.1, h.2⟩

theorem vertex_separation :
    Function.Injective (fun j => (gluedVertexX lower upper j, gluedHeight lower upper j)) := by
  intro i j same
  have x := congrArg Prod.fst same
  have y := congrArg Prod.snd same
  change gluedVertexX lower upper i = gluedVertexX lower upper j at x
  change gluedHeight lower upper i = gluedHeight lower upper j at y
  induction i using Fin.addCases <;> induction j using Fin.addCases
  case left.left v z =>
    rw [x_left, x_left] at x
    rw [height_left, height_left] at y
    exact congrArg (Fin.castAdd R) (lower.vertex_separation (Prod.ext x ((halfHeight_strictMono 0).injective y)))
  case left.right v z =>
    rw [height_left, height_right] at y
    exact ((lower_inside (lower := lower) v).2.not_ge (by rw [y]; exact (upper_inside (upper := upper) z).1.le)).elim
  case right.left v z =>
    rw [height_right, height_left] at y
    exact ((lower_inside (lower := lower) z).2.not_ge (by rw [← y]; exact (upper_inside (upper := upper) v).1.le)).elim
  case right.right v z =>
    rw [x_right, x_right] at x
    rw [height_right, height_right] at y
    exact congrArg (Fin.natAdd L) (upper.vertex_separation (Prod.ext x ((halfHeight_strictMono 1).injective y)))

theorem start_attached (w : Fin W) (j : Fin (L + R)) (start : gluedStart lower w = some j) :
    (gluedWire m w).x (gluedHeight lower upper j) = gluedVertexX lower upper j := by
  induction j using Fin.addCases with
  | left v =>
    rw [height_left, x_left, wire_left m w (lower_inside (lower := lower) v).2.le, unscale]
    exact lower.start_attached w v ((start_left w v).mp start)
  | right v => exact (start_not_right w v start).elim

theorem finish_attached (w : Fin W) (j : Fin (L + R)) (finish : gluedFinish upper w = some j) :
    (gluedWire m w).x (gluedHeight lower upper j) = gluedVertexX lower upper j := by
  induction j using Fin.addCases with
  | left v => exact (finish_not_left w v finish).elim
  | right v =>
    rw [height_right, x_right, wire_right m w (upper_inside (upper := upper) v).1.le, unscale]
    exact upper.finish_attached w v ((finish_right w v).mp finish)

theorem avoids_vertex (w : Fin W) (j : Fin (L + R))
    (active : gluedHeight lower upper j ∈ Set.Ioo (jointLower lower upper w) (jointUpper lower upper w)) :
    (gluedWire m w).x (gluedHeight lower upper j) ≠ gluedVertexX lower upper j := by
  induction j using Fin.addCases with
  | left v =>
    rw [height_left] at active
    have inside := lower_inside (lower := lower) v
    have hit := left_active m inside.2 active.1
    rw [unscale] at hit
    rw [height_left, x_left, wire_left m w inside.2.le, unscale]
    exact lower.avoids_vertex w v hit
  | right v =>
    rw [height_right] at active
    have inside := upper_inside (upper := upper) v
    have hit := right_active m inside.1 active.2
    rw [unscale] at hit
    rw [height_right, x_right, wire_right m w inside.1.le, unscale]
    exact upper.avoids_vertex w v hit

/-- Distinct glued wires retain their horizontal order on their common
open height interval. This also covers comparisons across the splice. -/
theorem transport_order {w z : Fin W} {a b : ℝ}
    (wa : a ∈ Set.Ioo (jointLower lower upper w) (jointUpper lower upper w))
    (za : a ∈ Set.Ioo (jointLower lower upper z) (jointUpper lower upper z))
    (wb : b ∈ Set.Ioo (jointLower lower upper w) (jointUpper lower upper w))
    (zb : b ∈ Set.Ioo (jointLower lower upper z) (jointUpper lower upper z))
    (ordered : (gluedWire m w).x a < (gluedWire m z).x a) :
    (gluedWire m w).x b < (gluedWire m z).x b := by
  let f := fun y => (gluedWire m w).x y - (gluedWire m z).x y
  have active {p q : ℝ} (ha : a ∈ Set.Ioo p q) (hb : b ∈ Set.Ioo p q)
      {y : ℝ} (hy : y ∈ Set.uIcc a b) : y ∈ Set.Ioo p q :=
    ⟨(lt_min ha.1 hb.1).trans_le hy.1, hy.2.trans_lt (max_lt ha.2 hb.2)⟩
  have continuous : ContinuousOn f (Set.uIcc a b) :=
    ((gluedWire m w).continuous.mono fun _ hy => Set.Ioo_subset_Icc_self (active wa wb hy)).sub
      ((gluedWire m z).continuous.mono fun _ hy => Set.Ioo_subset_Icc_self (active za zb hy))
  by_contra! reversed
  have zero : 0 ∈ Set.uIcc (f a) (f b) :=
    ⟨(min_le_left ..).trans (sub_nonpos.mpr ordered.le),
      (sub_nonneg.mpr reversed).trans (le_max_right ..)⟩
  obtain ⟨y, hy, collide⟩ := intermediate_value_uIcc continuous zero
  exact separated_wires m (ne_of_apply_ne (fun j => (gluedWire m j).x a) ordered.ne)
    (active wa wb hy) (Set.Ioo_subset_Icc_self (active za zb hy)) (sub_eq_zero.mp collide)

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
