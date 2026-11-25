module

public import Silmaril.Semantics.RuntimeWires.ProgressiveStripSwap.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap

open ProgressiveGraph OrderedKnots
abbrev Time := SlabIsotopy.Time

private theorem fraction_zero {a b x : ℝ} (ab : a < b) (h : x ≤ a) : fraction a b x = 0 := by
  unfold fraction
  rw [max_eq_left]
  exact min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sub_nonneg.mpr ab.le))

private theorem fraction_one {a b x : ℝ} (ab : a < b) (h : b ≤ x) : fraction a b x = 1 := by
  unfold fraction
  rw [min_eq_left ((le_div_iff₀ (sub_pos.mpr ab)).mpr (by linarith)), max_eq_right zero_le_one]

def weight (s : SwapStrip) (x : ℝ) : ℝ :=
  min (fraction s.left s.coreLeft x) (fraction (-s.right) (-s.coreRight) (-x))

private theorem fraction_range (a b x : ℝ) : fraction a b x ∈ Set.Icc 0 1 :=
  ⟨le_max_left .., max_le zero_le_one (min_le_left ..)⟩

theorem weight_range (s : SwapStrip) (x : ℝ) : weight s x ∈ Set.Icc 0 1 :=
  ⟨le_min (fraction_range ..).1 (fraction_range ..).1,
    (min_le_left ..).trans (fraction_range ..).2⟩

theorem weight_zero (s : SwapStrip) {x : ℝ} (h : x ∉ s.support) : weight s x = 0 := by
  by_cases hl : x ≤ s.left
  · unfold weight
    rw [fraction_zero s.left_gap hl, min_eq_left (fraction_range ..).1]
  · have hr : s.right ≤ x := le_of_not_gt fun hr => h ⟨lt_of_not_ge hl, hr⟩
    unfold weight
    rw [fraction_zero (neg_lt_neg s.right_gap) (neg_le_neg hr), min_eq_right (fraction_range ..).1]

theorem weight_one (s : SwapStrip) {x : ℝ} (h : x ∈ s.core) : weight s x = 1 := by
  unfold weight
  rw [fraction_one s.left_gap h.1, fraction_one (neg_lt_neg s.right_gap) (neg_le_neg h.2), min_self]

theorem weight_continuous (s : SwapStrip) : Continuous (weight s) := by
  unfold weight fraction
  fun_prop

theorem core_support (s : SwapStrip) {x : ℝ} (h : x ∈ s.core) : x ∈ s.support :=
  ⟨s.left_gap.trans_le h.1, h.2.trans_lt s.right_gap⟩

theorem support_disjoint (s : SwapStrips) {x : ℝ} (hl : x ∈ s.left.support) : x ∉ s.right.support :=
  fun hr => (hl.2.trans_le s.ordered).not_ge hr.1.le

theorem region_unique (s : SwapStrips) {r q : StripRegion} {x : ℝ}
    (h : x ∈ s.region r) (k : x ∈ s.region q) : r = q := by
  cases r <;> cases q
  · rfl
  · exact (support_disjoint s (core_support s.left h) (core_support s.right k)).elim
  · exact (k (Or.inl (core_support s.left h))).elim
  · exact (support_disjoint s (core_support s.left k) (core_support s.right h)).elim
  · rfl
  · exact (k (Or.inr (core_support s.right h))).elim
  · exact (h (Or.inl (core_support s.left k))).elim
  · exact (h (Or.inr (core_support s.right k))).elim
  · rfl

/-- Move the interior height knot in each vertical fibre. The taper regions
blend to the reference midpoint, and the ambient map is the identity there
when the input and output knots agree. -/
def anchor (s : SwapStrips) (a b x : ℝ) : ℝ :=
  (1 - weight s.left x - weight s.right x) * (1 / 2) + weight s.left x * a + weight s.right x * b

theorem anchor_left (s : SwapStrips) {x : ℝ} (h : x ∈ s.left.core) (a b : ℝ) : anchor s a b x = a := by
  rw [anchor, weight_one _ h, weight_zero _ (support_disjoint s (core_support s.left h))]
  ring

theorem anchor_right (s : SwapStrips) {x : ℝ} (h : x ∈ s.right.core) (a b : ℝ) : anchor s a b x = b := by
  rw [anchor, weight_one _ h, weight_zero _ (fun hl => support_disjoint s hl (core_support s.right h))]
  ring

theorem anchor_exterior (s : SwapStrips) {x : ℝ} (h : x ∈ s.region .exterior) (a b : ℝ) : anchor s a b x = 1 / 2 := by
  rw [anchor, weight_zero _ (fun hl => h (Or.inl hl)), weight_zero _ (fun hr => h (Or.inr hr))]
  ring

theorem anchor_inside (s : SwapStrips) {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (x : ℝ) :
    anchor s a b x ∈ Set.Ioo 0 1 := by
  have hl := weight_range s.left x
  have hr := weight_range s.right x
  have sum : 0 ≤ 1 - weight s.left x - weight s.right x := by
    by_cases mem : x ∈ s.left.support
    · rw [weight_zero _ (support_disjoint s mem)]
      linarith [hl.2]
    · rw [weight_zero _ mem]
      linarith [hr.2]
  let lo := min (1 / 2 : ℝ) (min a b)
  let hi := max (1 / 2 : ℝ) (max a b)
  have hlo : 0 < lo := lt_min (by norm_num) (lt_min ha.1 hb.1)
  have hhi : hi < 1 := max_lt (by norm_num) (max_lt ha.2 hb.2)
  have h₁ : lo ≤ anchor s a b x := by
    have hhalf : lo ≤ 1 / 2 := min_le_left ..
    have hleft : lo ≤ a := (min_le_right ..).trans (min_le_left ..)
    have hright : lo ≤ b := (min_le_right ..).trans (min_le_right ..)
    unfold anchor
    nlinarith [mul_le_mul_of_nonneg_left hhalf sum,
      mul_le_mul_of_nonneg_left hleft hl.1, mul_le_mul_of_nonneg_left hright hr.1]
  have h₂ : anchor s a b x ≤ hi := by
    have hhalf : 1 / 2 ≤ hi := le_max_left ..
    have hleft : a ≤ hi := (le_max_left ..).trans (le_max_right ..)
    have hright : b ≤ hi := (le_max_right ..).trans (le_max_right ..)
    unfold anchor
    nlinarith [mul_le_mul_of_nonneg_left hhalf sum,
      mul_le_mul_of_nonneg_left hleft hl.1, mul_le_mul_of_nonneg_left hright hr.1]
  exact ⟨hlo.trans_le h₁, h₂.trans_lt hhi⟩

def knots (a : ℝ) : Fin 3 → ℝ := ![0, a, 1]

theorem knots_increasing {a : ℝ} (ha : a ∈ Set.Ioo 0 1) : StrictMono (knots a) := by
  intro i j less
  fin_cases i <;> fin_cases j
  all_goals norm_num [Fin.lt_def] at less
  · exact ha.1
  · exact zero_lt_one
  · exact ha.2

def heightMap {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) : ℝ ≃ₜ ℝ :=
  OrderedKnots.homeomorph (knots_increasing ha) (knots_increasing hb)

theorem heightMap_apply {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (y : ℝ) :
    heightMap ha hb y = transfer (knots a) (knots b) y :=
  homeomorph_apply _ _ _

theorem heightMap_inv {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (y : ℝ) :
    (heightMap ha hb).symm y = heightMap hb ha y :=
  (homeomorph_symm_apply (knots_increasing ha) (knots_increasing hb) y).trans (heightMap_apply hb ha y).symm

theorem heightMap_increasing {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) :
    StrictMono (heightMap ha hb) := by
  intro x y h
  rw [heightMap_apply, heightMap_apply]
  exact transfer_strictMono (knots_increasing ha) (knots_increasing hb) h

theorem heightMap_outside {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) {y : ℝ}
    (h : y ≤ 0 ∨ 1 ≤ y) : heightMap ha hb y = y := by
  rw [heightMap_apply]
  rcases h with lo | hi
  · rw [transfer_left (knots_increasing ha) (show y ≤ knots a 0 from lo)]
    change 0 + (y - 0) = y
    ring
  · rw [transfer_right (knots_increasing ha) (show knots a (Fin.last 2) ≤ y from hi)]
    change 1 + (y - 1) = y
    ring

theorem heightMap_middle {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) : heightMap ha hb a = b := by
  rw [heightMap_apply]
  exact transfer_knot (knots_increasing ha) (1 : Fin 3)

theorem heightMap_self {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (y : ℝ) : heightMap ha ha y = y := by
  rw [heightMap_apply, transfer_self (knots_increasing ha)]

section TimeDependent

variable (s : SwapStrips) {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)

theorem lerp_inside {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (t : Time) :
    interpolate a b t.val ∈ Set.Ioo 0 1 := by
  have ht := t.property
  unfold interpolate
  constructor
  · by_cases h : t.val = 0
    · simp [h, ha.1]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) ha.1.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) hb.1)
  · have h : 0 < (1 - t.val) * (1 - a) + t.val * (1 - b) := by
      by_cases h : t.val = 0
      · simp [h, sub_pos.mpr ha.2]
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.2]) (by linarith [ha.2]))
          (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) (sub_pos.mpr hb.2))
    nlinarith

def movingAnchor (t : Time) (x : ℝ) : ℝ := anchor s (interpolate a b t.val) (interpolate b a t.val) x

include ha hb in
theorem movingAnchor_inside (t : Time) (x : ℝ) : movingAnchor s (a := a) (b := b) t x ∈ Set.Ioo 0 1 :=
  anchor_inside s (lerp_inside ha hb t) (lerp_inside hb ha t) x

theorem base_continuous {P : Type*} [TopologicalSpace P] {x : P → ℝ} (cx : Continuous x) :
    Continuous (fun p => anchor s a b (x p)) := by
  unfold anchor
  have cl := (weight_continuous s.left).comp cx
  have cr := (weight_continuous s.right).comp cx
  fun_prop

theorem moving_continuous {P : Type*} [TopologicalSpace P] {t : P → Time} {x : P → ℝ}
    (ct : Continuous t) (cx : Continuous x) : Continuous (fun p => movingAnchor s (a := a) (b := b) (t p) (x p)) := by
  unfold movingAnchor anchor interpolate
  have cl := (weight_continuous s.left).comp cx
  have cr := (weight_continuous s.right).comp cx
  have c := continuous_subtype_val.comp ct
  fun_prop

theorem knots_continuous {P : Type*} [TopologicalSpace P] {x : P → ℝ} (cx : Continuous x) (i : Fin 3) :
    Continuous (fun p => knots (x p) i) := by
  fin_cases i <;> first | exact continuous_const | exact cx

def fibre (t : Time) (x : ℝ) : ℝ ≃ₜ ℝ :=
  heightMap (anchor_inside s ha hb x) (movingAnchor_inside s ha hb t x)

theorem continuous_fibre : Continuous (fun z : Time × (ℝ × ℝ) => fibre s ha hb z.1 z.2.1 z.2.2) := by
  simp only [fibre, heightMap_apply]
  exact continuous_transfer (knots_continuous (base_continuous s (continuous_fst.comp continuous_snd)))
    (knots_continuous (moving_continuous s continuous_fst (continuous_fst.comp continuous_snd)))
    (fun z => knots_increasing (anchor_inside s ha hb z.2.1)) (continuous_snd.comp continuous_snd)

theorem continuous_fibre_inv : Continuous (fun z : Time × (ℝ × ℝ) => (fibre s ha hb z.1 z.2.1).symm z.2.2) := by
  simp only [fibre, heightMap_inv, heightMap_apply]
  exact continuous_transfer
    (knots_continuous (moving_continuous s continuous_fst (continuous_fst.comp continuous_snd)))
    (knots_continuous (base_continuous s (continuous_fst.comp continuous_snd)))
    (fun z => knots_increasing (movingAnchor_inside s ha hb z.1 z.2.1)) (continuous_snd.comp continuous_snd)

def forward (z : Time × (ℝ × ℝ)) : ℝ × ℝ :=
  (z.2.1, fibre s ha hb z.1 z.2.1 z.2.2)

def backward (z : Time × (ℝ × ℝ)) : ℝ × ℝ :=
  (z.2.1, (fibre s ha hb z.1 z.2.1).symm z.2.2)

theorem forward_continuous : Continuous (forward s ha hb) :=
  (continuous_fst.comp continuous_snd).prodMk (continuous_fibre s ha hb)

theorem backward_continuous : Continuous (backward s ha hb) :=
  (continuous_fst.comp continuous_snd).prodMk (continuous_fibre_inv s ha hb)

def ambient (t : Time) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := forward s ha hb ∘ fun z => (t, z)
  invFun := backward s ha hb ∘ fun z => (t, z)
  left_inv z := Prod.ext rfl ((fibre s ha hb t z.1).symm_apply_apply z.2)
  right_inv z := Prod.ext rfl ((fibre s ha hb t z.1).apply_symm_apply z.2)
  continuous_toFun := (forward_continuous s ha hb).comp
    (show Continuous (fun z : ℝ × ℝ => (t, z)) from continuous_const.prodMk continuous_id)
  continuous_invFun := (backward_continuous s ha hb).comp
    (show Continuous (fun z : ℝ × ℝ => (t, z)) from continuous_const.prodMk continuous_id)

theorem ambient_continuous : Continuous (fun z : Time × (ℝ × ℝ) => ambient s ha hb z.1 z.2) :=
  forward_continuous s ha hb

theorem ambient_continuous_inv : Continuous (fun z : Time × (ℝ × ℝ) => (ambient s ha hb z.1).symm z.2) :=
  backward_continuous s ha hb

theorem ambient_caps (t : Time) (z : ℝ × ℝ) (h : z.2 ≤ 0 ∨ 1 ≤ z.2) : ambient s ha hb t z = z := by
  apply Prod.ext
  · rfl
  · exact heightMap_outside (anchor_inside s ha hb z.1) (movingAnchor_inside s ha hb t z.1) h

theorem ambient_zero (z : ℝ × ℝ) : ambient s ha hb ⟨0, le_rfl, zero_le_one⟩ z = z := by
  apply Prod.ext
  · rfl
  change heightMap (anchor_inside s ha hb z.1) (movingAnchor_inside s ha hb _ z.1) z.2 = _
  have eq : movingAnchor s (a := a) (b := b) ⟨0, le_rfl, zero_le_one⟩ z.1 = anchor s a b z.1 := by
    simp [movingAnchor, interpolate]
  rw [heightMap_apply, eq, transfer_self (knots_increasing (anchor_inside s ha hb z.1))]

def regionMap (t : Time) : StripRegion → ℝ ≃ₜ ℝ
  | .left => heightMap ha (lerp_inside ha hb t)
  | .right => heightMap hb (lerp_inside hb ha t)
  | .exterior => Homeomorph.refl ℝ

theorem region_increasing (t : Time) (r : StripRegion) : StrictMono (regionMap ha hb t r) := by
  cases r
  · exact heightMap_increasing ha (lerp_inside ha hb t)
  · exact heightMap_increasing hb (lerp_inside hb ha t)
  · exact strictMono_id

theorem region_caps (t : Time) (r : StripRegion) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : regionMap ha hb t r y = y := by
  cases r
  · exact heightMap_outside ha (lerp_inside ha hb t) h
  · exact heightMap_outside hb (lerp_inside hb ha t) h
  · rfl

theorem ambient_region (t : Time) (r : StripRegion) (z : ℝ × ℝ) (h : z.1 ∈ s.region r) :
    ambient s ha hb t z = (z.1, regionMap ha hb t r z.2) := by
  apply Prod.ext
  · rfl
  change fibre s ha hb t z.1 z.2 = regionMap ha hb t r z.2
  cases r
  · rw [fibre, heightMap_apply, movingAnchor, anchor_left s h, anchor_left s h]
    exact (heightMap_apply ha (lerp_inside ha hb t) z.2).symm
  · rw [fibre, heightMap_apply, movingAnchor, anchor_right s h, anchor_right s h]
    exact (heightMap_apply hb (lerp_inside hb ha t) z.2).symm
  · rw [fibre, heightMap_apply, movingAnchor, anchor_exterior s h, anchor_exterior s h,
      transfer_self (knots_increasing (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1))]
    rfl

end TimeDependent
end Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap
