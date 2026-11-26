module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveStripSwap.Ambient
import all Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveStripSwap.Ambient
import Mathlib.Tactic.Linarith

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap

open ProgressiveGraph OrderedKnots

private theorem lower_formula {a b y : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hy : y ∈ Set.Icc 0 a) : heightMap ha hb y = b * (y / a) := by
  rw [heightMap_apply, transfer_segment (knots_increasing ha) (0 : Fin 2) hy]
  change 0 + (b - 0) * ((y - 0) / (a - 0)) = b * (y / a)
  rw [zero_add, sub_zero, sub_zero, sub_zero]

private theorem upper_formula {a b y : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hy : y ∈ Set.Icc a 1) : heightMap ha hb y = b + (1 - b) * ((y - a) / (1 - a)) := by
  rw [heightMap_apply, transfer_segment (knots_increasing ha) (1 : Fin 2) hy]
  rfl

private theorem chord_mem {a b x y t : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc 0 1) : (1 - t) * x + t * y ∈ Set.Icc a b := by
  have nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  constructor
  · calc
      a = (1 - t) * a + t * a := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.1 nonneg) (mul_le_mul_of_nonneg_left hy.1 ht.1)
  · calc
      (1 - t) * x + t * y ≤ (1 - t) * b + t * b :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 nonneg) (mul_le_mul_of_nonneg_left hy.2 ht.1)
      _ = b := by ring

private theorem heightMap_affine {a b x y t : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) (skip : a ∉ Set.Ioo x y) (ht : t ∈ Set.Icc 0 1) :
    heightMap ha hb ((1 - t) * x + t * y) = (1 - t) * heightMap ha hb x + t * heightMap ha hb y := by
  by_cases below : y ≤ a
  · have xmem : x ∈ Set.Icc 0 a := ⟨hx, hxy.le.trans below⟩
    have ymem : y ∈ Set.Icc 0 a := ⟨hx.trans hxy.le, below⟩
    rw [lower_formula ha hb (chord_mem xmem ymem ht), lower_formula ha hb xmem, lower_formula ha hb ymem]
    ring
  · have above : a ≤ x := le_of_not_gt (fun h => skip ⟨h, lt_of_not_ge below⟩)
    have xmem : x ∈ Set.Icc a 1 := ⟨above, hxy.le.trans hy⟩
    have ymem : y ∈ Set.Icc a 1 := ⟨above.trans hxy.le, hy⟩
    rw [upper_formula ha hb (chord_mem xmem ymem ht), upper_formula ha hb xmem, upper_formula ha hb ymem]
    ring

section

variable {a b : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (time : Time) (r : StripRegion)

def movingKnot (a b : ℝ) (time : Time) : StripRegion → ℝ
  | .left => interpolate a b time.val
  | .right => interpolate b a time.val
  | .exterior => 1 / 2

theorem inverse_increasing : StrictMono (regionMap ha hb time r).symm := by
  intro x y less
  apply (region_increasing ha hb time r).lt_iff_lt.mp
  simpa only [Homeomorph.apply_symm_apply] using less

private theorem inverse_affine {x y t : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y)
    (skip : movingKnot a b time r ∉ Set.Ioo x y) (ht : t ∈ Set.Icc 0 1) :
    (regionMap ha hb time r).symm ((1 - t) * x + t * y) =
      (1 - t) * (regionMap ha hb time r).symm x + t * (regionMap ha hb time r).symm y := by
  cases r
  · simp only [regionMap, heightMap_inv]
    exact heightMap_affine (lerp_inside ha hb time) ha hx hy hxy skip ht
  · simp only [regionMap, heightMap_inv]
    exact heightMap_affine (lerp_inside hb ha time) hb hx hy hxy skip ht
  · rfl

/-- Reparametrize one entire wire by the height map on its strip. A finite
subdivision is obtained from the old knots and the new interior height knot. -/
def moveWire {lo hi : ℝ} (w : Wire lo hi) (hlo : 0 ≤ lo) (hhi : hi ≤ 1) :
    Wire (regionMap ha hb time r lo) (regionMap ha hb time r hi) where
  x y := w.x ((regionMap ha hb time r).symm y)
  increasing := region_increasing ha hb time r w.increasing
  continuous := by
    let f := regionMap ha hb time r
    apply w.continuous.comp f.symm.continuous.continuousOn
    intro y hy
    have sg := inverse_increasing ha hb time r
    exact ⟨(f.symm_apply_apply lo).symm.trans_le (sg.monotone hy.1),
      (sg.monotone hy.2).trans_eq (f.symm_apply_apply hi)⟩
  polygonal := by
    classical
    let f := regionMap ha hb time r
    let g := f.symm
    have sf := region_increasing ha hb time r
    have sg := inverse_increasing ha hb time r
    obtain ⟨K, hK⟩ := w.polygonal
    refine ⟨insert (movingKnot a b time r) (K.image f), ?_⟩
    intro x hx y hy less skip t ht
    have xlo : 0 ≤ x := (region_caps ha hb time r (Or.inl (le_refl 0))).symm.trans_le
      ((sf.monotone hlo).trans hx.1)
    have yhi : y ≤ 1 := (hy.2.trans (sf.monotone hhi)).trans_eq
      (region_caps ha hb time r (Or.inr (le_refl 1)))
    have maps (z : ℝ) (hz : z ∈ Set.Icc (f lo) (f hi)) : g z ∈ Set.Icc lo hi :=
      ⟨(f.symm_apply_apply lo).symm.trans_le (sg.monotone hz.1),
        (sg.monotone hz.2).trans_eq (f.symm_apply_apply hi)⟩
    have avoids (k : ℝ) (hk : k ∈ K) : k ∉ Set.Ioo (g x) (g y) := by
      intro kmem
      apply skip (f k) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hk))
      exact ⟨(f.apply_symm_apply x).symm.trans_lt (sf kmem.1),
        (sf kmem.2).trans_eq (f.apply_symm_apply y)⟩
    rw [inverse_affine ha hb time r xlo yhi less (skip _ (Finset.mem_insert_self ..)) ht]
    exact hK (g x) (maps x hx) (g y) (maps y hy) (sg less) avoids t ht

end
end Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap
