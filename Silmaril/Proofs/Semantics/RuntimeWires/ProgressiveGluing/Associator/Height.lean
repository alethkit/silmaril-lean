module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator.Height

open ProgressiveGraph ProgressiveGraph.OrderedKnots

def left : Fin 6 → ℝ := ![0, 1 / 16, 1 / 8, 1 / 4, 1 / 2, 1]
def right : Fin 6 → ℝ := ![0, 1 / 4, 1 / 2, 5 / 8, 3 / 4, 1]

theorem left_order : StrictMono left := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> norm_num [left, Fin.castSucc, Fin.succ]

theorem right_order : StrictMono right := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> norm_num [right, Fin.castSucc, Fin.succ]

def affine (a b t : ℝ) : ℝ := a + (b - a) * t

theorem carries_slab (i : Fin 5) {h : ℝ} (hh : h ∈ Set.Icc (0 : ℝ) 1) :
    transfer left right (affine (left i.castSucc) (left i.succ) h) =
      affine (right i.castSucc) (right i.succ) h := by
  have pos := sub_pos.mpr (left_order (Fin.castSucc_lt_succ (i := i)))
  have inside : affine (left i.castSucc) (left i.succ) h ∈
      Set.Icc (left i.castSucc) (left i.succ) := by
    unfold affine
    exact ⟨by nlinarith [mul_nonneg pos.le hh.1],
      by nlinarith [mul_nonneg pos.le (sub_nonneg.mpr hh.2)]⟩
  rw [transfer_segment left_order i inside]
  unfold affine
  have ratio :
      (left i.castSucc + (left i.succ - left i.castSucc) * h - left i.castSucc) /
        (left i.succ - left i.castSucc) = h := by
    field_simp
    ring
  rw [ratio]

def lower (y : ℝ) : ℝ := halfHeight 0 (halfHeight 0 y)
def collar (y : ℝ) : ℝ := halfHeight 0 (halfHeight 1 y)
def upper (y : ℝ) : ℝ := halfHeight 1 y

def leftPlacement : Fin 5 → ℝ → ℝ :=
  ![lower ∘ lower, lower ∘ collar, lower ∘ upper, collar, upper]

def rightPlacement : Fin 5 → ℝ → ℝ :=
  ![lower, collar, upper ∘ lower, upper ∘ collar, upper ∘ upper]

theorem leftPlacement_eq (i : Fin 5) (y : ℝ) :
    leftPlacement i y = affine (left i.castSucc) (left i.succ) y := by
  fin_cases i <;> norm_num [leftPlacement, left, lower, collar, upper, halfHeight, affine, Fin.castSucc, Fin.succ] <;> ring

theorem rightPlacement_eq (i : Fin 5) (y : ℝ) :
    rightPlacement i y = affine (right i.castSucc) (right i.succ) y := by
  fin_cases i <;> norm_num [rightPlacement, right, lower, collar, upper, halfHeight, affine, Fin.castSucc, Fin.succ] <;> ring

theorem carries_placement (i : Fin 5) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    transfer left right (leftPlacement i y) = rightPlacement i y := by
  rw [leftPlacement_eq, rightPlacement_eq, carries_slab i hy]

def heightMap : ℝ ≃ₜ ℝ := homeomorph left_order right_order

def pointMap : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.refl ℝ).prodCongr heightMap

theorem point_placement (i : Fin 5) (x : ℝ) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    pointMap (x, leftPlacement i y) = (x, rightPlacement i y) := by
  change (x, heightMap (leftPlacement i y)) = _
  rw [heightMap, homeomorph_apply, carries_placement i hy]

theorem outside_height {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : heightMap y = y := by
  rw [heightMap, homeomorph_apply]
  rcases h with h | h
  · rw [transfer_left left_order (by simpa [left] using h)]
    norm_num [left, right]
  · rw [transfer_right left_order (by simpa [left, Fin.last] using h)]
    norm_num [left, right, Fin.last]

end Silmaril.RuntimeWires.Proofs.CollarAssociator.Height
