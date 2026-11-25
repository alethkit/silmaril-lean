module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapUnits

open ProgressiveGraph ProgressiveGraph.OrderedKnots

/-- Both distances are measured from the cap where the pad is inserted. -/
structure Padding where
  width : ℝ
  amount : ℝ
  width_inside : width ∈ Set.Ioo 0 1
  amount_inside : amount ∈ Set.Ioo 0 1

namespace Padding

variable (p : Padding)

def placed (y : ℝ) : ℝ := p.amount + (1 - p.amount) * y
def localHeight (z : ℝ) : ℝ := (z - p.amount) / (1 - p.amount)
def clip (y : ℝ) : ℝ := max 0 (min p.width y)

theorem placed_strict : StrictMono p.placed := by
  intro x y h
  unfold placed
  exact add_lt_add_right (mul_lt_mul_of_pos_left h (sub_pos.mpr p.amount_inside.2)) _

theorem placed_zero : p.placed 0 = p.amount := by simp [placed]
theorem placed_one : p.placed 1 = 1 := by simp [placed]

theorem local_placed (y : ℝ) : p.localHeight (p.placed y) = y := by
  have h := ne_of_gt (sub_pos.mpr p.amount_inside.2)
  unfold localHeight placed
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ h]

theorem placed_local (y : ℝ) : p.placed (p.localHeight y) = y := by
  have h := ne_of_gt (sub_pos.mpr p.amount_inside.2)
  unfold localHeight placed
  field_simp
  ring

theorem local_strict : StrictMono p.localHeight := by
  intro x y h
  exact p.placed_strict.lt_iff_lt.mp (by rwa [placed_local, placed_local])

theorem clip_mem (y : ℝ) : p.clip y ∈ Set.Icc 0 p.width :=
  ⟨le_max_left .., max_le p.width_inside.1.le (min_le_left ..)⟩

theorem clip_eq {y : ℝ} (h : y ∈ Set.Icc 0 p.width) : p.clip y = y := by
  simp [clip, min_eq_right h.2, max_eq_right h.1]

theorem clip_low {y : ℝ} (h : y ≤ 0) : p.clip y = 0 :=
  max_eq_left ((min_le_right _ _).trans h)

theorem clip_high {y : ℝ} (h : p.width ≤ y) : p.clip y = p.width := by
  simp [clip, min_eq_left h, max_eq_right p.width_inside.1.le]

theorem local_continuous : Continuous p.localHeight :=
  (continuous_id.sub continuous_const).div_const _

theorem clip_continuous : Continuous p.clip :=
  continuous_const.max (continuous_const.min continuous_id)

def sourceKnots : Fin 3 → ℝ := ![0, p.width, 1]
def targetKnots : Fin 3 → ℝ := ![0, p.placed p.width, 1]

theorem placed_width : p.placed p.width ∈ Set.Ioo p.amount 1 := by
  constructor
  · rw [← p.placed_zero]
    exact p.placed_strict p.width_inside.1
  · rw [← p.placed_one]
    exact p.placed_strict p.width_inside.2

theorem source_order : StrictMono p.sourceKnots := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact p.width_inside.1
  · exact p.width_inside.2

theorem target_order : StrictMono p.targetKnots := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact p.amount_inside.1.trans p.placed_width.1
  · exact p.placed_width.2

def stretch : ℝ ≃ₜ ℝ := OrderedKnots.homeomorph p.source_order p.target_order

theorem stretch_strict : StrictMono p.stretch := by
  intro x y h
  simp only [stretch, homeomorph_apply]
  exact transfer_strictMono p.source_order p.target_order h

theorem stretch_outside {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : p.stretch y = y := by
  rw [stretch, homeomorph_apply]
  rcases h with h | h
  · rw [transfer_left p.source_order (by simpa [sourceKnots] using h)]
    simp [targetKnots, sourceKnots]
  · rw [transfer_right p.source_order (by simpa [sourceKnots, Fin.last] using h)]
    simp [targetKnots, sourceKnots, Fin.last]

theorem stretch_core {y : ℝ} (h : y ∈ Set.Icc p.width 1) :
    p.stretch y = p.placed y := by
  rw [stretch, homeomorph_apply, transfer_segment p.source_order (1 : Fin 2) h]
  change p.placed p.width + (1 - p.placed p.width) * ((y - p.width) / (1 - p.width)) = _
  unfold placed
  have hn := ne_of_gt (sub_pos.mpr p.width_inside.2)
  field_simp
  ring

theorem stretch_unit {y : ℝ} (h : y ∈ Set.Icc (0 : ℝ) 1) :
    p.stretch y ∈ Set.Icc 0 1 := by
  have lo := p.stretch_strict.monotone h.1
  have hi := p.stretch_strict.monotone h.2
  rw [p.stretch_outside (.inl le_rfl)] at lo
  rw [p.stretch_outside (.inr le_rfl)] at hi
  exact ⟨lo, hi⟩

theorem local_le_width {y : ℝ} (h : y ≤ p.width) :
    p.localHeight (p.stretch y) ≤ p.width := by
  have heq := p.stretch_core ⟨le_rfl, p.width_inside.2.le⟩
  have hle := p.local_strict.monotone (p.stretch_strict.monotone h)
  rwa [heq, local_placed] at hle

theorem local_nonneg {z : ℝ} (h : p.amount ≤ z) : 0 ≤ p.localHeight z := by
  have h' := p.local_strict.monotone (p.placed_zero.symm ▸ h)
  rwa [local_placed] at h'

theorem horizontal_clip_outside {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) :
    p.clip y = p.clip (p.localHeight (p.stretch y)) := by
  rw [p.stretch_outside h]
  rcases h with h | h
  · have low : y ≤ p.placed 0 := p.placed_zero.symm ▸ h.trans p.amount_inside.1.le
    have hy := p.local_strict.monotone low
    rw [local_placed] at hy
    rw [p.clip_low h, p.clip_low hy]
  · have high : p.placed 1 ≤ y := p.placed_one.symm ▸ h
    have hy := p.local_strict.monotone high
    rw [local_placed] at hy
    rw [p.clip_high (p.width_inside.2.le.trans h), p.clip_high (p.width_inside.2.le.trans hy)]

theorem horizontal_clip_core {y : ℝ} (h : y ∈ Set.Icc p.width 1) :
    p.clip y = p.clip (p.localHeight (p.stretch y)) := by
  rw [p.stretch_core h, p.local_placed]

section Knots

variable {n : ℕ} {k : ℝ → Fin (n + 1) → ℝ}
variable (hc : ∀ i, Continuous (fun y => k y i)) (ho : ∀ y, StrictMono (k y))

def straighten : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (transfer (k (p.clip z.2)) (k (p.clip (p.localHeight (p.stretch z.2)))) z.1, z.2)
  invFun z := (transfer (k (p.clip (p.localHeight (p.stretch z.2)))) (k (p.clip z.2)) z.1, z.2)
  left_inv _ := Prod.ext (transfer_inverse (ho _) (ho _) _) rfl
  right_inv _ := Prod.ext (transfer_inverse (ho _) (ho _) _) rfl
  continuous_toFun := (continuous_transfer
    (fun i => (hc i).comp (p.clip_continuous.comp continuous_snd))
    (fun i => (hc i).comp (p.clip_continuous.comp ((p.local_continuous).comp
      (p.stretch.continuous.comp continuous_snd))))
    (fun _ => ho _) continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_transfer
    (fun i => (hc i).comp (p.clip_continuous.comp ((p.local_continuous).comp
      (p.stretch.continuous.comp continuous_snd))))
    (fun i => (hc i).comp (p.clip_continuous.comp continuous_snd))
    (fun _ => ho _) continuous_fst).prodMk continuous_snd

def radiusPlane : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (p.straighten hc ho).trans ((Homeomorph.refl ℝ).prodCongr p.stretch)

theorem radiusPlane_apply (x y : ℝ) :
    p.radiusPlane hc ho (x, y) =
      (transfer (k (p.clip y)) (k (p.clip (p.localHeight (p.stretch y)))) x, p.stretch y) := rfl

theorem radiusPlane_core (x : ℝ) {y : ℝ} (h : y ∈ Set.Icc p.width 1) :
    p.radiusPlane hc ho (x, y) = (x, p.placed y) := by
  rw [radiusPlane_apply, ← p.horizontal_clip_core h, transfer_self (ho _), p.stretch_core h]

theorem radiusPlane_outside (x : ℝ) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) :
    p.radiusPlane hc ho (x, y) = (x, y) := by
  rw [radiusPlane_apply, ← p.horizontal_clip_outside h, transfer_self (ho _), p.stretch_outside h]

theorem radiusPlane_slot (j : Fin (n + 1)) (y : ℝ) :
    p.radiusPlane hc ho (k (p.clip y) j, y) =
      (k (p.clip (p.localHeight (p.stretch y))) j, p.stretch y) := by
  rw [radiusPlane_apply, transfer_knot (ho _)]

end Knots
end Padding
end Silmaril.RuntimeWires.Proofs.CapUnits
