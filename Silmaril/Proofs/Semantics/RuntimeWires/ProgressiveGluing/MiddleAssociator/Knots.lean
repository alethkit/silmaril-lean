module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Ambient
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.MiddleAssociator

open ProgressiveGraph OrderedKnots
open EmptyWhiskering (slab sourceTime targetTime source_unit target_unit sourceTime_continuous
  targetTime_continuous source_on target_on times_agree)

def leftKnots : Fin 4 → ℝ := ![0, 1 / 4, 1 / 2, 1]
def rightKnots : Fin 4 → ℝ := ![0, 1 / 2, 3 / 4, 1]

theorem left_strict : StrictMono leftKnots :=
  HorizontalComparison.knots_strict (by norm_num) (by norm_num) (by norm_num)

theorem right_strict : StrictMono rightKnots :=
  HorizontalComparison.knots_strict (by norm_num) (by norm_num) (by norm_num)

def horizontal : ℝ → ℝ := transfer leftKnots rightKnots

theorem horizontal_strict : StrictMono horizontal := transfer_strictMono left_strict right_strict

/-- The idle-left block expands from a quarter to a half. -/
theorem horizontal_left {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    horizontal (ActiveStrip.left.place (ActiveStrip.left.place x)) = ActiveStrip.left.place x := by
  have inside : ActiveStrip.left.place (ActiveStrip.left.place x) ∈
      Set.Icc (leftKnots (0 : Fin 3).castSucc) (leftKnots (0 : Fin 3).succ) := by
    change x / 2 / 2 ∈ Set.Icc (0 : ℝ) (1 / 4)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  unfold horizontal
  rw [transfer_segment left_strict (0 : Fin 3) inside]
  simp only [leftKnots, rightKnots, ActiveStrip.place, Fin.castSucc, Fin.succ]
  norm_num
  ring

/-- The middle block keeps its width and moves into the next quarter. -/
theorem horizontal_middle {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    horizontal (ActiveStrip.left.place (ActiveStrip.right.place x)) =
      ActiveStrip.right.place (ActiveStrip.left.place x) := by
  have inside : ActiveStrip.left.place (ActiveStrip.right.place x) ∈
      Set.Icc (leftKnots (1 : Fin 3).castSucc) (leftKnots (1 : Fin 3).succ) := by
    change (1 + x) / 2 / 2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  unfold horizontal
  rw [transfer_segment left_strict (1 : Fin 3) inside]
  simp only [leftKnots, rightKnots, ActiveStrip.place, Fin.castSucc, Fin.succ]
  norm_num
  ring

/-- The idle-right block compresses from a half to a quarter. -/
theorem horizontal_right {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    horizontal (ActiveStrip.right.place x) = ActiveStrip.right.place (ActiveStrip.right.place x) := by
  have inside : ActiveStrip.right.place x ∈
      Set.Icc (leftKnots (2 : Fin 3).castSucc) (leftKnots (2 : Fin 3).succ) := by
    change (1 + x) / 2 ∈ Set.Icc (1 / 2 : ℝ) 1
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  unfold horizontal
  rw [transfer_segment left_strict (2 : Fin 3) inside]
  simp only [leftKnots, rightKnots, ActiveStrip.place, Fin.castSucc, Fin.succ]
  norm_num
  ring

def knotsAt (t : ℝ) (i : Fin 4) : ℝ := interpolate (leftKnots i) (rightKnots i) t

theorem knotsAt_strict {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : StrictMono (knotsAt t) := by
  intro i j h
  unfold knotsAt interpolate
  rcases ht.1.eq_or_lt with h₀ | h₀
  · simp [← h₀, left_strict h]
  · exact add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left (left_strict h).le (sub_nonneg.mpr ht.2))
      (mul_lt_mul_of_pos_left (right_strict h) h₀)

theorem knotsAt_continuous (i : Fin 4) : Continuous (fun t => knotsAt t i) := by
  unfold knotsAt interpolate
  fun_prop

theorem transfer_knotsAt {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (t : ℝ) :
    transfer leftKnots (knotsAt t) x = interpolate x (horizontal x) t := by
  obtain ⟨i, hi⟩ := exists_segment (a := leftKnots) x hx.1 hx.2.le
  let segment (knots : Fin 4 → ℝ) :=
    knots i.castSucc + (knots i.succ - knots i.castSucc) *
      ((x - leftKnots i.castSucc) / (leftKnots i.succ - leftKnots i.castSucc))
  have self : segment leftKnots = x :=
    (transfer_segment left_strict i hi).symm.trans (transfer_self left_strict x)
  have moved : segment rightKnots = horizontal x :=
    (transfer_segment left_strict i hi).symm
  calc
    transfer leftKnots (knotsAt t) x = segment (knotsAt t) := transfer_segment left_strict i hi
    _ = interpolate (segment leftKnots) (segment rightKnots) t := by
      unfold segment knotsAt interpolate
      ring
    _ = _ := congrArg₂ (fun a b => interpolate a b t) self moved

theorem transfer_track {a b x : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    transfer (knotsAt a) (knotsAt b) (interpolate x (horizontal x) a) =
      interpolate x (horizontal x) b := by
  have back := transfer_inverse left_strict (knotsAt_strict ha) x
  rw [← transfer_knotsAt hx a, ← transfer_knotsAt hx b]
  obtain ⟨i, hi⟩ := exists_segment (a := leftKnots) x hx.1 hx.2.le
  have hi' : transfer leftKnots (knotsAt a) x ∈ Set.Icc (knotsAt a i.castSucc) (knotsAt a i.succ) := by
    have mono := (transfer_strictMono left_strict (knotsAt_strict ha)).monotone
    exact ⟨(transfer_knot (b := knotsAt a) left_strict i.castSucc) ▸ mono hi.1,
      (transfer_knot (b := knotsAt a) left_strict i.succ) ▸ mono hi.2⟩
  have eq := transfer_segment (b := leftKnots) (knotsAt_strict ha) i hi'
  rw [back] at eq
  have ratio : (transfer leftKnots (knotsAt a) x - knotsAt a i.castSucc) /
      (knotsAt a i.succ - knotsAt a i.castSucc) =
      (x - leftKnots i.castSucc) / (leftKnots i.succ - leftKnots i.castSucc) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr (left_strict (Fin.castSucc_lt_succ (i := i)))))).mpr
    linarith only [eq]
  rw [transfer_segment (knotsAt_strict ha) i hi', ratio]
  exact (transfer_segment left_strict i hi).symm

/-- At each common slab height, carry the source coordinates to the target
coordinates along the prescribed piecewise-affine interpolation. -/
def ambient : CapHomeomorph where
  plane :=
    { toFun z := (transfer (knotsAt (sourceTime z.2)) (knotsAt (targetTime z.2)) z.1, z.2)
      invFun z := (transfer (knotsAt (targetTime z.2)) (knotsAt (sourceTime z.2)) z.1, z.2)
      left_inv z := Prod.ext (transfer_inverse (knotsAt_strict (source_unit z.2))
        (knotsAt_strict (target_unit z.2)) z.1) rfl
      right_inv z := Prod.ext (transfer_inverse (knotsAt_strict (target_unit z.2))
        (knotsAt_strict (source_unit z.2)) z.1) rfl
      continuous_toFun :=
        (continuous_transfer
          (fun i => (knotsAt_continuous i).comp (sourceTime_continuous.comp continuous_snd))
          (fun i => (knotsAt_continuous i).comp (targetTime_continuous.comp continuous_snd))
          (fun z => knotsAt_strict (source_unit z.2)) continuous_fst).prodMk continuous_snd
      continuous_invFun :=
        (continuous_transfer
          (fun i => (knotsAt_continuous i).comp (targetTime_continuous.comp continuous_snd))
          (fun i => (knotsAt_continuous i).comp (sourceTime_continuous.comp continuous_snd))
          (fun z => knotsAt_strict (target_unit z.2)) continuous_fst).prodMk continuous_snd }
  height := Homeomorph.refl _
  increasing := strictMono_id
  height_eq _ := rfl
  outside z h := by
    change (transfer (knotsAt (sourceTime z.2)) (knotsAt (targetTime z.2)) z.1, z.2) = z
    rw [← times_agree h, transfer_self (knotsAt_strict (source_unit z.2))]

theorem ambient_track {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (k : Fin 5) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ambient.plane (interpolate x (horizontal x) (if k = 4 then t else 0), slab k t) =
      (interpolate x (horizontal x) (if k = 0 then t else 1), slab k t) := by
  rw [← source_on k ht, ← target_on k ht]
  exact Prod.ext (transfer_track (source_unit (slab k t)) hx) rfl

theorem interpolate_zero (x z : ℝ) : interpolate x z 0 = x := by simp [interpolate]
theorem interpolate_one (x z : ℝ) : interpolate x z 1 = z := by simp [interpolate]

end Silmaril.RuntimeWires.Proofs.MiddleAssociator
