module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Silmaril.RuntimeWires.Proofs.OrderedKnots

open ProgressiveGraph.OrderedKnots

theorem fraction_zero {a b x : ℝ} (ab : a < b) (hx : x ≤ a) : fraction a b x = 0 := by
  unfold fraction
  exact max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hx) (sub_nonneg.mpr ab.le)))

theorem fraction_one {a b x : ℝ} (ab : a < b) (hx : b ≤ x) : fraction a b x = 1 := by
  unfold fraction
  rw [min_eq_left ((one_le_div (sub_pos.mpr ab)).mpr (sub_le_sub_right hx _)), max_eq_right zero_le_one]

theorem fraction_between {a b x : ℝ} (ab : a < b) (hx : x ∈ Set.Icc a b) :
    fraction a b x = (x - a) / (b - a) := by
  unfold fraction
  rw [min_eq_right ((div_le_one (sub_pos.mpr ab)).mpr (sub_le_sub_right hx.2 _)),
    max_eq_right (div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr ab.le))]

variable {n : ℕ} {a b : Fin (n + 1) → ℝ}

theorem left_tail (ha : StrictMono a) {x : ℝ} (h : x ≤ a 0) :
    transfer a b x = b 0 + (x - a 0) := by
  unfold transfer
  have zero : (∑ i : Fin n, (b i.succ - b i.castSucc) * fraction (a i.castSucc) (a i.succ) x) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [fraction_zero (ha (Fin.castSucc_lt_succ (i := i))) (h.trans (ha.monotone (Fin.zero_le _))), mul_zero]
  rw [zero, add_zero, min_eq_left (sub_nonpos.mpr h),
    max_eq_right (sub_nonpos.mpr (h.trans (ha.monotone (Fin.zero_le _)))), add_zero]

theorem difference_on_segment (ha : StrictMono a) (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Icc (a j.castSucc) (a j.succ)) :
    transfer a b x = transfer a b (a j.castSucc) +
      (b j.succ - b j.castSucc) * ((x - a j.castSucc) / (a j.succ - a j.castSucc)) := by
  classical
  have h₀ : a 0 ≤ a j.castSucc := ha.monotone (Fin.zero_le _)
  have hₙ : a j.succ ≤ a (Fin.last n) := ha.monotone (Fin.le_last _)
  let f (x : ℝ) (i : Fin n) := (b i.succ - b i.castSucc) * fraction (a i.castSucc) (a i.succ) x
  have other (i : Fin n) (ne : i ≠ j) : f x i = f (a j.castSucc) i := by
    rcases lt_or_gt_of_ne ne with before | after
    · have le : a i.succ ≤ a j.castSucc := ha.monotone (by
        exact Fin.le_def.mpr (Nat.succ_le_of_lt before))
      simp only [f, fraction_one (ha (Fin.castSucc_lt_succ (i := i))) le,
        fraction_one (ha (Fin.castSucc_lt_succ (i := i))) (le.trans hx.1)]
    · have le : a j.succ ≤ a i.castSucc := ha.monotone (by
        exact Fin.le_def.mpr (Nat.succ_le_of_lt after))
      simp only [f, fraction_zero (ha (Fin.castSucc_lt_succ (i := i))) (hx.2.trans le),
        fraction_zero (ha (Fin.castSucc_lt_succ (i := i))) ((ha (Fin.castSucc_lt_succ (i := j))).le.trans le)]
  have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have sums : ∑ i ∈ Finset.univ.erase j, f x i = ∑ i ∈ Finset.univ.erase j, f (a j.castSucc) i :=
    Finset.sum_congr rfl fun i hi => other i (Finset.ne_of_mem_erase hi)
  unfold transfer
  simp only [min_eq_right (sub_nonneg.mpr (h₀.trans hx.1)), min_eq_right (sub_nonneg.mpr h₀),
    max_eq_right (sub_nonpos.mpr (hx.2.trans hₙ)),
    max_eq_right (sub_nonpos.mpr ((ha (Fin.castSucc_lt_succ (i := j))).le.trans hₙ)), add_zero]
  suffices eq : (∑ i, f x i) = (∑ i, f (a j.castSucc) i) +
      (b j.succ - b j.castSucc) * ((x - a j.castSucc) / (a j.succ - a j.castSucc)) by
    linarith only [eq]
  rw [← Finset.sum_erase_add Finset.univ (f x) hj, ← Finset.sum_erase_add Finset.univ (f (a j.castSucc)) hj, sums]
  simp only [f, fraction_zero (ha (Fin.castSucc_lt_succ (i := j))) le_rfl,
    fraction_between (ha (Fin.castSucc_lt_succ (i := j))) hx, mul_zero, add_zero]

theorem knot (ha : StrictMono a) (j : Fin (n + 1)) : transfer a b (a j) = b j := by
  induction j using Fin.induction with
  | zero => rw [left_tail ha le_rfl, sub_self, add_zero]
  | succ j ih =>
    rw [difference_on_segment ha j ⟨(ha (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩, ih,
      div_self (sub_ne_zero.mpr (ha (Fin.castSucc_lt_succ (i := j))).ne'), mul_one]
    ring

theorem segment (ha : StrictMono a) (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Icc (a j.castSucc) (a j.succ)) :
    transfer a b x = b j.castSucc +
      (b j.succ - b j.castSucc) * ((x - a j.castSucc) / (a j.succ - a j.castSucc)) := by
  rw [difference_on_segment ha j hx, knot ha]

theorem right_tail (ha : StrictMono a) {x : ℝ} (h : a (Fin.last n) ≤ x) :
    transfer a b x = b (Fin.last n) + (x - a (Fin.last n)) := by
  rw [← knot (a := a) (b := b) ha (Fin.last n)]
  have h₀ := ha.monotone (Fin.zero_le (Fin.last n))
  unfold transfer
  simp only [min_eq_right (sub_nonneg.mpr (h₀.trans h)), min_eq_right (sub_nonneg.mpr h₀),
    max_eq_left (sub_nonneg.mpr h), sub_self, max_self, add_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have hi := ha.monotone (Fin.le_last i.succ)
  rw [fraction_one (ha (Fin.castSucc_lt_succ (i := i))) hi,
    fraction_one (ha (Fin.castSucc_lt_succ (i := i))) (hi.trans h)]

theorem covered (x : ℝ) (hx : a 0 < x) (hy : x ≤ a (Fin.last n)) :
    ∃ j : Fin n, x ∈ Set.Icc (a j.castSucc) (a j.succ) := by
  classical
  let hasKnot : ∃ j, x ≤ a j := ⟨Fin.last n, hy⟩
  let j := Fin.find (fun j => x ≤ a j) hasKnot
  have positive : 0 < j := (Fin.find_pos hasKnot).mpr hx.not_ge
  have right : x ≤ a j := Fin.find_spec hasKnot
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr (Fin.ne_of_gt positive)
  refine ⟨i, ?_, hi ▸ right⟩
  have before : i.castSucc < j := hi ▸ Fin.castSucc_lt_succ (i := i)
  exact (lt_of_not_ge (Fin.find_min hasKnot before)).le

end Silmaril.RuntimeWires.Proofs.OrderedKnots
