module

public import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Defs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSwap

open Silmaril.RuntimeWires.Polygonal

theorem continuous_rescale : Continuous (fun p : ℝ × ℝ => BoxPair.rescale p.1 p.2) := by
  unfold BoxPair.rescale
  fun_prop

private theorem decompose (y : ℝ) :
    min y 1 + (min (max y 1) 2 - 1) + max (y - 2) 0 = y := by
  rcases le_total y 1 with h | h
  · simp [min_eq_left h, max_eq_right h, show (1 : ℝ) ≤ 2 by norm_num,
      max_eq_right (show y - 2 ≤ 0 by linarith)]
  · rw [min_eq_right h, max_eq_left h]
    rcases le_total y 2 with h' | h'
    · rw [min_eq_left h', max_eq_right (sub_nonpos.mpr h')]
      ring
    · rw [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]
      ring

theorem rescale_strict {h : ℝ} (hh : h ∈ BoxAltitude) : StrictMono (BoxPair.rescale h) := by
  have hl : 0 < h := zero_lt_one.trans_le hh.1
  have hr : 0 < (5 - h) / 4 := by linarith [hh.2]
  intro y z hyz
  have lo := min_le_min_right (1 : ℝ) hyz.le
  have mid := min_le_min_right (2 : ℝ) (max_le_max_right (1 : ℝ) hyz.le)
  have hi := max_le_max_right (0 : ℝ) (sub_le_sub_right hyz.le 2)
  have hlo := mul_le_mul_of_nonneg_left lo hl.le
  have hhi := mul_le_mul_of_nonneg_left hi hr.le
  change BoxPair.rescale h y < BoxPair.rescale h z
  unfold BoxPair.rescale
  by_contra! hsum
  have elo := mul_left_cancel₀ hl.ne' (le_antisymm hlo (by linarith))
  have emid : min (max y 1) 2 = min (max z 1) 2 := le_antisymm mid (by linarith)
  have ehi := mul_left_cancel₀ hr.ne' (le_antisymm hhi (by linarith))
  rw [← decompose y, ← decompose z, elo, emid, ehi] at hyz
  exact lt_irrefl _ hyz

theorem rescale_zero (h : ℝ) : BoxPair.rescale h 0 = 0 := by
  norm_num [BoxPair.rescale, min_def, max_def]

theorem rescale_one (h : ℝ) : BoxPair.rescale h 1 = h := by
  norm_num [BoxPair.rescale, min_def, max_def]

theorem rescale_two (h : ℝ) : BoxPair.rescale h 2 = h + 1 := by
  norm_num [BoxPair.rescale, min_def, max_def]

theorem rescale_six (h : ℝ) : BoxPair.rescale h 6 = 6 := by
  norm_num [BoxPair.rescale, min_def, max_def]
  ring

theorem rescale_identity (y : ℝ) : BoxPair.rescale 1 y = y := by
  simpa [BoxPair.rescale, show ((5 - 1) / 4 : ℝ) = 1 by norm_num] using decompose y

theorem rescale_image {h a b : ℝ} (hh : h ∈ BoxAltitude) (hab : a ≤ b) :
    BoxPair.rescale h '' Set.Icc a b = Set.Icc (BoxPair.rescale h a) (BoxPair.rescale h b) := by
  have hc : Continuous (BoxPair.rescale h) :=
    continuous_rescale.comp (continuous_const.prodMk continuous_id)
  refine Set.Subset.antisymm ?_ (hc.continuousOn.surjOn_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩)
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(rescale_strict hh).monotone hy.1, (rescale_strict hh).monotone hy.2⟩

end Silmaril.RuntimeWires.Proofs.PolygonalSwap
