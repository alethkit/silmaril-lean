module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Silmaril.RuntimeWires.Proofs.OrderedKnots

open ProgressiveGraph.OrderedKnots

variable {n : ℕ} {a b : Fin (n + 1) → ℝ}

theorem transfer_monotone (ha : StrictMono a) (hb : StrictMono b) : Monotone (transfer a b) := by
  intro x y xy
  have sums :
      (∑ i : Fin n, (b i.succ - b i.castSucc) * fraction (a i.castSucc) (a i.succ) x) ≤
        ∑ i : Fin n, (b i.succ - b i.castSucc) * fraction (a i.castSucc) (a i.succ) y := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hb Fin.castSucc_lt_succ).le)
    unfold fraction
    exact max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right xy _)
      (sub_nonneg.mpr (ha Fin.castSucc_lt_succ).le)))
  unfold transfer
  exact add_le_add (add_le_add (add_le_add le_rfl (min_le_min (sub_le_sub_right xy _) le_rfl)) sums)
    (max_le_max (sub_le_sub_right xy _) le_rfl)

theorem inverse (ha : StrictMono a) (hb : StrictMono b) (x : ℝ) :
    transfer b a (transfer a b x) = x := by
  have mono := transfer_monotone ha hb
  rcases le_or_gt x (a 0) with low | low
  · have image : transfer a b x ≤ b 0 := (mono low).trans_eq (knot ha _)
    rw [left_tail hb image, left_tail ha low]
    ring
  rcases le_or_gt (a (Fin.last n)) x with high | high
  · have image : b (Fin.last n) ≤ transfer a b x := (knot ha _).symm.trans_le (mono high)
    rw [right_tail hb image, right_tail ha high]
    ring
  obtain ⟨j, inside⟩ := covered x low high.le
  have image : transfer a b x ∈ Set.Icc (b j.castSucc) (b j.succ) :=
    ⟨(knot ha _).symm.trans_le (mono inside.1), (mono inside.2).trans_eq (knot ha _)⟩
  rw [segment hb j image, segment ha j inside]
  have left := sub_ne_zero.mpr (ha (Fin.castSucc_lt_succ (i := j))).ne'
  have right := sub_ne_zero.mpr (hb (Fin.castSucc_lt_succ (i := j))).ne'
  field_simp
  ring

theorem transfer_strictMono (ha : StrictMono a) (hb : StrictMono b) : StrictMono (transfer a b) :=
  (transfer_monotone ha hb).strictMono_of_injective (Function.LeftInverse.injective (inverse ha hb))

theorem transfer_self (ha : StrictMono a) (x : ℝ) : transfer a a x = x := by
  rcases le_or_gt x (a 0) with low | low
  · rw [left_tail ha low]
    ring
  rcases le_or_gt (a (Fin.last n)) x with high | high
  · rw [right_tail ha high]
    ring
  obtain ⟨j, h⟩ := covered x low high.le
  rw [segment ha j h]
  have pos := sub_ne_zero.mpr (ha (Fin.castSucc_lt_succ (i := j))).ne'
  field_simp
  ring

/-- Both the forward and inverse formulas apply to continuous families of knots. -/
theorem continuous_transfer {P : Type*} [TopologicalSpace P] {a b : P → Fin (n + 1) → ℝ}
    {x : P → ℝ} (ca : ∀ i, Continuous (fun p => a p i)) (cb : ∀ i, Continuous (fun p => b p i))
    (ha : ∀ p, StrictMono (a p)) (cx : Continuous x) :
    Continuous (fun p => transfer (a p) (b p) (x p)) := by
  have term (i : Fin n) :
      Continuous (fun p => (b p i.succ - b p i.castSucc) * fraction (a p i.castSucc) (a p i.succ) (x p)) := by
    have nonzero (p : P) : a p i.succ - a p i.castSucc ≠ 0 :=
      sub_ne_zero.mpr (ha p Fin.castSucc_lt_succ).ne'
    unfold fraction
    exact ((cb i.succ).sub (cb i.castSucc)).mul
      (continuous_const.max (continuous_const.min
        ((cx.sub (ca i.castSucc)).div ((ca i.succ).sub (ca i.castSucc)) nonzero)))
  unfold transfer
  exact (((cb 0).add ((cx.sub (ca 0)).min continuous_const)).add
    (continuous_finsetSum _ fun i _ => term i)).add ((cx.sub (ca (Fin.last n))).max continuous_const)

noncomputable def homeomorph (ha : StrictMono a) (hb : StrictMono b) : ℝ ≃ₜ ℝ where
  toFun := transfer a b
  invFun := transfer b a
  left_inv := inverse ha hb
  right_inv := inverse hb ha
  continuous_toFun := continuous_transfer (fun _ => continuous_const) (fun _ => continuous_const)
    (fun _ => ha) continuous_id
  continuous_invFun := continuous_transfer (fun _ => continuous_const) (fun _ => continuous_const)
    (fun _ => hb) continuous_id

end Silmaril.RuntimeWires.Proofs.OrderedKnots
