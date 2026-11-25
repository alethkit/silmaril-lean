module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Ambient
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Ambient
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Recoordination
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Knots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CentralRecoordination

open ProgressiveGraph OrderedKnots
open EmptyWhiskering (slab sourceTime targetTime source_unit target_unit sourceTime_continuous
  targetTime_continuous source_on target_on times_agree)
open HorizontalPlacement (place_strict)
open scoped BigOperators

section Transfer

variable {n : ℕ} {a b : Fin (n + 1) → ℝ}

def blend (a b : Fin (n + 1) → ℝ) (t : ℝ) (i : Fin (n + 1)) : ℝ :=
  interpolate (a i) (b i) t

theorem blend_strict (ha : StrictMono a) (hb : StrictMono b)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : StrictMono (blend a b t) := by
  intro i j h
  unfold blend interpolate
  rcases ht.1.eq_or_lt with zero | pos
  · simp [← zero, ha h]
  · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (ha h).le (sub_nonneg.mpr ht.2))
      (mul_lt_mul_of_pos_left (hb h) pos)

theorem blend_continuous (i : Fin (n + 1)) : Continuous (fun t => blend a b t i) := by
  unfold blend interpolate
  fun_prop

/-- Transfer is affine in the target knots at every evaluation point. -/
theorem transfer_blend (ha : StrictMono a) (x t : ℝ) :
    transfer a (blend a b t) x = interpolate x (transfer a b x) t := by
  have sums :
      (∑ i : Fin n, (blend a b t i.succ - blend a b t i.castSucc) * fraction (a i.castSucc) (a i.succ) x) =
        (1 - t) * (∑ i : Fin n, (a i.succ - a i.castSucc) * fraction (a i.castSucc) (a i.succ) x) +
          t * (∑ i : Fin n, (b i.succ - b i.castSucc) * fraction (a i.castSucc) (a i.succ) x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold blend interpolate
    ring
  calc
    _ = interpolate (transfer a a x) (transfer a b x) t := by
      unfold transfer
      rw [sums]
      unfold blend interpolate
      ring
    _ = _ := by rw [transfer_self ha]

/-- A common ordered knot enumeration makes the two affine transfers
compose on each segment and on the unit-slope tails. -/
theorem transfer_comp (ha : StrictMono a) (hb : StrictMono b) (c : Fin (n + 1) → ℝ) (x : ℝ) :
    transfer b c (transfer a b x) = transfer a c x := by
  rcases le_or_gt x (a 0) with low | middle
  · have h : b 0 + (x - a 0) ≤ b 0 := by linarith
    rw [transfer_left (b := b) ha low, transfer_left hb h, transfer_left ha low]
    ring
  rcases le_or_gt (a (Fin.last n)) x with high | middleHigh
  · have h : b (Fin.last n) ≤ b (Fin.last n) + (x - a (Fin.last n)) := by linarith
    rw [transfer_right (b := b) ha high, transfer_right hb h, transfer_right ha high]
    ring
  obtain ⟨i, hi⟩ := exists_segment x middle middleHigh.le
  have moved : transfer a b x ∈ Set.Icc (b i.castSucc) (b i.succ) := by
    have mono := (transfer_strictMono ha hb).monotone
    exact ⟨(transfer_knot (b := b) ha i.castSucc) ▸ mono hi.1,
      (transfer_knot (b := b) ha i.succ) ▸ mono hi.2⟩
  have inv := transfer_segment (b := a) hb i moved
  rw [transfer_inverse ha hb] at inv
  have ratio : (transfer a b x - b i.castSucc) / (b i.succ - b i.castSucc) =
      (x - a i.castSucc) / (a i.succ - a i.castSucc) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr (ha (Fin.castSucc_lt_succ (i := i)))))).mpr
    linarith only [inv]
  rw [transfer_segment hb i moved, ratio]
  exact (transfer_segment ha i hi).symm

theorem transfer_blend_track (ha : StrictMono a) (hb : StrictMono b)
    (x t u : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    transfer (blend a b t) (blend a b u) (interpolate x (transfer a b x) t) =
      interpolate x (transfer a b x) u := by
  rw [← transfer_blend ha x t, ← transfer_blend ha x u, transfer_comp ha (blend_strict ha hb ht)]

end Transfer

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a a' : FixedCap S}
variable (side : ActiveStrip) (h : a.types = a'.types)

abbrev interpolation := FixedCap.interpolationDrawing h

def idleKnots (t : ℝ) (i : Fin (a.profile.size + 2)) : ℝ :=
  side.opposite.place (CapRecoordination.frameKnots (interpolation h) rfl t i)

theorem idle_knots_strict (t : ℝ) : StrictMono (idleKnots side h t) :=
  (place_strict side.opposite).comp (CapRecoordination.knots_strict (interpolation h) rfl t)

theorem first_knot (t : ℝ) : idleKnots side h t 0 = side.opposite.place 0 :=
  congrArg side.opposite.place (CapRecoordination.first_knot (interpolation h) rfl t)

theorem last_knot (t : ℝ) :
    idleKnots side h t (Fin.last (a.profile.size + 1)) = side.opposite.place 1 :=
  congrArg side.opposite.place (CapRecoordination.last_knot (interpolation h) rfl t)

theorem contact_knot (i : Fin a.profile.size) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    idleKnots side h t i.succ.castSucc =
      side.opposite.place (interpolate (a.profile.x i) (a'.profile.x (FixedCap.recoordinationSlots h i)) t) := by
  have unclip : CapRecoordination.coords (interpolation h) rfl t i = (interpolation h).drawing.x i t :=
    congrArg ((interpolation h).drawing.x i) (CapRecoordination.clip_in ht)
  exact congrArg side.opposite.place
    ((CapRecoordination.wire_knot (interpolation h) rfl t i).trans
      (unclip.trans (FixedCap.interpolation_x h i t)))

def horizontal : ℝ → ℝ := transfer (idleKnots side h 0) (idleKnots side h 1)

theorem horizontal_strict : StrictMono (horizontal side h) :=
  transfer_strictMono (idle_knots_strict side h 0) (idle_knots_strict side h 1)

theorem horizontal_idle (i : Fin a.profile.size) :
    horizontal side h (side.opposite.place (a.profile.x i)) =
      side.opposite.place (a'.profile.x (FixedCap.recoordinationSlots h i)) := by
  have lo := contact_knot side h i (t := 0) ⟨le_rfl, zero_le_one⟩
  have hi := contact_knot side h i (t := 1) ⟨zero_le_one, le_rfl⟩
  rw [MiddleAssociator.interpolate_zero] at lo
  rw [MiddleAssociator.interpolate_one] at hi
  rw [← lo, ← hi]
  exact transfer_knot (idle_knots_strict side h 0) i.succ.castSucc

theorem horizontal_active {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    horizontal side h (side.place x) = side.place x := by
  unfold horizontal
  cases side
  · have low : ActiveStrip.left.place x ≤ idleKnots .left h 0 0 := by
      rw [first_knot]
      change x / 2 ≤ (1 + 0) / 2
      linarith [hx.2]
    rw [transfer_left (idle_knots_strict .left h 0) low, first_knot, first_knot]
    ring
  · have high : idleKnots .right h 0 (Fin.last (a.profile.size + 1)) ≤ ActiveStrip.right.place x := by
      rw [last_knot]
      change 1 / 2 ≤ (1 + x) / 2
      linarith [hx.1]
    rw [transfer_right (idle_knots_strict .right h 0) high, last_knot, last_knot]
    ring

abbrev knotsAt := blend (idleKnots side h 0) (idleKnots side h 1)

theorem knotsAt_strict {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    StrictMono (knotsAt side h t) :=
  blend_strict (idle_knots_strict side h 0) (idle_knots_strict side h 1) ht

def ambient : CapHomeomorph where
  plane :=
    { toFun z := (transfer (knotsAt side h (sourceTime z.2)) (knotsAt side h (targetTime z.2)) z.1, z.2)
      invFun z := (transfer (knotsAt side h (targetTime z.2)) (knotsAt side h (sourceTime z.2)) z.1, z.2)
      left_inv z := Prod.ext (transfer_inverse (knotsAt_strict side h (source_unit z.2))
        (knotsAt_strict side h (target_unit z.2)) z.1) rfl
      right_inv z := Prod.ext (transfer_inverse (knotsAt_strict side h (target_unit z.2))
        (knotsAt_strict side h (source_unit z.2)) z.1) rfl
      continuous_toFun :=
        (continuous_transfer
          (fun i => (blend_continuous i).comp (sourceTime_continuous.comp continuous_snd))
          (fun i => (blend_continuous i).comp (targetTime_continuous.comp continuous_snd))
          (fun z => knotsAt_strict side h (source_unit z.2)) continuous_fst).prodMk continuous_snd
      continuous_invFun :=
        (continuous_transfer
          (fun i => (blend_continuous i).comp (targetTime_continuous.comp continuous_snd))
          (fun i => (blend_continuous i).comp (sourceTime_continuous.comp continuous_snd))
          (fun z => knotsAt_strict side h (target_unit z.2)) continuous_fst).prodMk continuous_snd }
  height := Homeomorph.refl _
  increasing := strictMono_id
  height_eq _ := rfl
  outside z hy := by
    change (transfer (knotsAt side h (sourceTime z.2)) (knotsAt side h (targetTime z.2)) z.1, z.2) = z
    rw [← times_agree hy, transfer_self (knotsAt_strict side h (source_unit z.2))]

theorem ambient_track (x : ℝ) (k : Fin 5) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (ambient side h).plane (interpolate x (horizontal side h x) (if k = 4 then t else 0), slab k t) =
      (interpolate x (horizontal side h x) (if k = 0 then t else 1), slab k t) := by
  rw [← source_on k ht, ← target_on k ht]
  exact Prod.ext (transfer_blend_track (idle_knots_strict side h 0) (idle_knots_strict side h 1)
    x _ _ (source_unit (slab k t))) rfl

end Silmaril.RuntimeWires.Proofs.CentralRecoordination
