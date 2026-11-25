module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Compression
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Height
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.EmptyWhiskering

open ProgressiveGraph OrderedKnots
open HorizontalComparison (InteriorRange knots knots_strict clamp)
open HorizontalPlacement (place_strict)

abbrev slab := CollarAssociator.Height.leftPlacement

/-- The placed deformation parameter on the source drawing. The change
of coordinates takes place entirely in the uppermost slab. -/
def sourceTime (y : ℝ) : ℝ := clamp 0 1 (2 * y - 1)

/-- The placed deformation parameter on the target drawing. The change
of coordinates takes place entirely in the lowest slab. -/
def targetTime (y : ℝ) : ℝ := clamp 0 1 (16 * y)

theorem clamp_unit (x : ℝ) : clamp 0 1 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp_at {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) : clamp 0 1 x = x := by
  rw [clamp, min_eq_right h.2, max_eq_right h.1]

theorem clamp_before {x : ℝ} (h : x ≤ 0) : clamp 0 1 x = 0 :=
  max_eq_left ((min_le_right _ _).trans h)

theorem clamp_after {x : ℝ} (h : 1 ≤ x) : clamp 0 1 x = 1 := by
  rw [clamp, min_eq_left h, max_eq_right zero_le_one]

theorem source_on (k : Fin 5) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    sourceTime (slab k t) = if k = 4 then t else 0 := by
  fin_cases k <;>
    norm_num [sourceTime, slab, CollarAssociator.Height.leftPlacement,
      CollarAssociator.Height.lower, CollarAssociator.Height.upper,
      CollarAssociator.Height.collar, halfHeight]
  all_goals first
    | exact clamp_before (by linarith [ht.2])
    | apply Eq.trans (congrArg (clamp 0 1) (by ring)); exact clamp_at ht

theorem target_on (k : Fin 5) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    targetTime (slab k t) = if k = 0 then t else 1 := by
  fin_cases k <;>
    norm_num [targetTime, slab, CollarAssociator.Height.leftPlacement,
      CollarAssociator.Height.lower, CollarAssociator.Height.upper,
      CollarAssociator.Height.collar, halfHeight]
  all_goals first
    | exact clamp_after (by linarith [ht.1])
    | apply Eq.trans (congrArg (clamp 0 1) (by ring)); exact clamp_at ht

theorem times_agree {y : ℝ} (outside : y ≤ 0 ∨ 1 ≤ y) : sourceTime y = targetTime y := by
  change clamp 0 1 (2 * y - 1) = clamp 0 1 (16 * y)
  rcases outside with low | high
  · rw [clamp_before (by linarith : 2 * y - 1 ≤ 0), clamp_before (by linarith : 16 * y ≤ 0)]
  · rw [clamp_after (by linarith : 1 ≤ 2 * y - 1), clamp_after (by linarith : 1 ≤ 16 * y)]

theorem source_unit (y : ℝ) : sourceTime y ∈ Set.Icc (0 : ℝ) 1 := clamp_unit _
theorem target_unit (y : ℝ) : targetTime y ∈ Set.Icc (0 : ℝ) 1 := clamp_unit _

def track (side : ActiveStrip) (t x : ℝ) : ℝ := interpolate x (side.place x) t

theorem track_zero (side : ActiveStrip) (x : ℝ) : track side 0 x = x := by
  simp [track, interpolate]

theorem track_one (side : ActiveStrip) (x : ℝ) : track side 1 x = side.place x := by
  simp [track, interpolate]

theorem track_strict (side : ActiveStrip) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    StrictMono (track side t) := by
  intro x z less
  have hplace := place_strict side less
  unfold track interpolate
  rcases ht.1.eq_or_lt with h | h
  · simp [← h, less]
  · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left less.le (sub_nonneg.mpr ht.2))
      (mul_lt_mul_of_pos_left hplace h)

theorem track_inside (side : ActiveStrip) {t x : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    track side t x ∈ Set.Ioo (0 : ℝ) 1 := by
  have lower := track_strict side ht hx.1
  have upper := track_strict side ht hx.2
  cases side <;> simp only [track, interpolate, ActiveStrip.place] at lower upper ⊢ <;>
    constructor <;> nlinarith [ht.1, ht.2]

theorem track_continuous (side : ActiveStrip) (x : ℝ) : Continuous (fun t => track side t x) := by
  unfold track interpolate
  fun_prop

theorem track_affine (side : ActiveStrip) (t x l r : ℝ) (h : l < r) :
    track side t l + (track side t r - track side t l) * ((x - l) / (r - l)) = track side t x := by
  cases side <;> unfold track interpolate ActiveStrip.place <;>
    field_simp [ne_of_gt (sub_pos.mpr h)] <;> ring

def frameKnots (side : ActiveStrip) (span : InteriorRange) (t : ℝ) : Fin 4 → ℝ :=
  knots 0 (track side t span.left) (track side t span.right) 1

theorem frame_order (side : ActiveStrip) (span : InteriorRange) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : StrictMono (frameKnots side span t) :=
  knots_strict
    (track_inside side ht ⟨span.left_inside, span.order.trans span.right_inside⟩).1
    (track_strict side ht span.order)
    (track_inside side ht ⟨span.left_inside.trans span.order, span.right_inside⟩).2

theorem frame_continuous (side : ActiveStrip) (span : InteriorRange) (i : Fin 4) :
    Continuous (fun t => frameKnots side span t i) := by
  fin_cases i
  · exact continuous_const
  · exact track_continuous side span.left
  · exact track_continuous side span.right
  · exact continuous_const

theorem transfer_track (side : ActiveStrip) (span : InteriorRange) {a b x : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc span.left span.right) :
    transfer (frameKnots side span a) (frameKnots side span b) (track side a x) = track side b x := by
  have m := (track_strict side ha).monotone
  rw [transfer_segment (frame_order side span ha) (1 : Fin 3) ⟨m hx.1, m hx.2⟩]
  change track side b span.left + (track side b span.right - track side b span.left) *
    ((track side a x - track side a span.left) /
      (track side a span.right - track side a span.left)) = _
  have affine := track_affine side a x span.left span.right span.order
  have positive := sub_pos.mpr (track_strict side ha span.order)
  have ratio : (track side a x - track side a span.left) /
      (track side a span.right - track side a span.left) = (x - span.left) / (span.right - span.left) := by
    apply (div_eq_iff (ne_of_gt positive)).mpr
    linarith [affine, mul_comm ((x - span.left) / (span.right - span.left))
      (track side a span.right - track side a span.left)]
  rw [ratio, track_affine side b x span.left span.right span.order]

theorem sourceTime_continuous : Continuous sourceTime := by
  unfold sourceTime clamp
  fun_prop

theorem targetTime_continuous : Continuous targetTime := by
  unfold targetTime clamp
  fun_prop

def ambient (side : ActiveStrip) (span : InteriorRange) : CapHomeomorph where
  plane :=
    { toFun z := (transfer (frameKnots side span (sourceTime z.2))
        (frameKnots side span (targetTime z.2)) z.1, z.2)
      invFun z := (transfer (frameKnots side span (targetTime z.2))
        (frameKnots side span (sourceTime z.2)) z.1, z.2)
      left_inv z := Prod.ext (transfer_inverse (frame_order side span (source_unit z.2))
        (frame_order side span (target_unit z.2)) z.1) rfl
      right_inv z := Prod.ext (transfer_inverse (frame_order side span (target_unit z.2))
        (frame_order side span (source_unit z.2)) z.1) rfl
      continuous_toFun :=
        (continuous_transfer
          (fun i => (frame_continuous side span i).comp (sourceTime_continuous.comp continuous_snd))
          (fun i => (frame_continuous side span i).comp (targetTime_continuous.comp continuous_snd))
          (fun z => frame_order side span (source_unit z.2)) continuous_fst).prodMk continuous_snd
      continuous_invFun :=
        (continuous_transfer
          (fun i => (frame_continuous side span i).comp (targetTime_continuous.comp continuous_snd))
          (fun i => (frame_continuous side span i).comp (sourceTime_continuous.comp continuous_snd))
          (fun z => frame_order side span (target_unit z.2)) continuous_fst).prodMk continuous_snd }
  height := Homeomorph.refl _
  increasing := strictMono_id
  height_eq _ := rfl
  outside z h := by
    change (transfer (frameKnots side span (sourceTime z.2))
      (frameKnots side span (targetTime z.2)) z.1, z.2) = z
    rw [← times_agree h, transfer_self (frame_order side span (source_unit z.2))]

theorem ambient_track (side : ActiveStrip) (span : InteriorRange) {x : ℝ}
    (hx : x ∈ Set.Icc span.left span.right) (k : Fin 5) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (ambient side span).plane (track side (if k = 4 then t else 0) x, slab k t) =
      (track side (if k = 0 then t else 1) x, slab k t) := by
  rw [← source_on k ht, ← target_on k ht]
  exact Prod.ext (transfer_track side span (source_unit (slab k t)) hx) rfl

end Silmaril.RuntimeWires.Proofs.EmptyWhiskering
