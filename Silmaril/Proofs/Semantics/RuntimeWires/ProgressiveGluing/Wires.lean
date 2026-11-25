module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph

theorem slab_mem {a b y offset : ℝ} (inside : y ∈ Set.Icc (halfHeight offset a) (halfHeight offset b)) :
    slabHeight offset y ∈ Set.Icc a b := by
  obtain ⟨low, high⟩ := inside
  dsimp only [halfHeight] at low high
  exact ⟨by dsimp only [slabHeight]; linarith, by dsimp only [slabHeight]; linarith⟩

theorem slab_mono (offset : ℝ) : StrictMono (slabHeight offset) := by
  intro a b hab
  unfold slabHeight
  linarith

theorem half_mono (offset : ℝ) : StrictMono (halfHeight offset) := by
  intro a b hab
  unfold halfHeight
  linarith

theorem scale_continuous {a b : ℝ} (w : Wire a b) (offset : ℝ) :
    ContinuousOn (w.x ∘ slabHeight offset) (Set.Icc (halfHeight offset a) (halfHeight offset b)) :=
  w.continuous.comp (by unfold slabHeight; fun_prop) (fun _ hy => slab_mem hy)

theorem scale_polygonal {a b : ℝ} (w : Wire a b) (offset : ℝ) :
    ∃ knots : Finset ℝ, ∀ l ∈ Set.Icc (halfHeight offset a) (halfHeight offset b),
      ∀ r ∈ Set.Icc (halfHeight offset a) (halfHeight offset b), l < r →
      (∀ k ∈ knots, k ∉ Set.Ioo l r) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (w.x ∘ slabHeight offset) ((1 - t) * l + t * r) =
        (1 - t) * (w.x ∘ slabHeight offset) l + t * (w.x ∘ slabHeight offset) r := by
  classical
  obtain ⟨knots, chord⟩ := w.polygonal
  refine ⟨knots.image (halfHeight offset), ?_⟩
  intro l hl r hr order uncut t ht
  have noKnot (k : ℝ) (hk : k ∈ knots) : k ∉ Set.Ioo (slabHeight offset l) (slabHeight offset r) := by
    intro hc
    apply uncut (halfHeight offset k) (Finset.mem_image_of_mem _ hk)
    exact ⟨by dsimp [halfHeight, slabHeight] at *; linarith [hc.1],
      by dsimp [halfHeight, slabHeight] at *; linarith [hc.2]⟩
  have affine : slabHeight offset ((1 - t) * l + t * r) =
      (1 - t) * slabHeight offset l + t * slabHeight offset r := by
    unfold slabHeight
    ring
  simpa only [Function.comp_apply, affine] using
    chord (slabHeight offset l) (slab_mem hl) (slabHeight offset r) (slab_mem hr)
      (slab_mono offset order) noKnot t ht

theorem splice_left {m : ℝ} {f g : ℝ → ℝ} {y : ℝ} (hy : y ≤ m) :
    spliceX m f g y = f y := by simp [spliceX, hy]

theorem splice_right {m : ℝ} {f g : ℝ → ℝ} (contact : f m = g m) {y : ℝ} (hy : m ≤ y) :
    spliceX m f g y = g y := by
  rcases hy.eq_or_lt with eq | lt
  · subst y
    simpa only [splice_left le_rfl] using contact
  · simp [spliceX, not_le.mpr lt]

theorem splice_continuous {a m b : ℝ} (lower : Wire a m) (upper : Wire m b)
    (contact : lower.x m = upper.x m) : ContinuousOn (spliceX m lower.x upper.x) (Set.Icc a b) := by
  have first : ContinuousOn (spliceX m lower.x upper.x) (Set.Icc a m) :=
    lower.continuous.congr (fun _ hy => splice_left hy.2)
  have last : ContinuousOn (spliceX m lower.x upper.x) (Set.Icc m b) :=
    upper.continuous.congr (fun _ hy => splice_right contact hy.1)
  rw [← Set.Icc_union_Icc_eq_Icc lower.increasing.le upper.increasing.le]
  exact first.union_of_isClosed last isClosed_Icc isClosed_Icc

theorem splice_polygonal {a m b : ℝ} (lower : Wire a m) (upper : Wire m b)
    (contact : lower.x m = upper.x m) :
    ∃ knots : Finset ℝ, ∀ l ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b,
      l < r → (∀ k ∈ knots, k ∉ Set.Ioo l r) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      spliceX m lower.x upper.x ((1 - t) * l + t * r) =
        (1 - t) * spliceX m lower.x upper.x l + t * spliceX m lower.x upper.x r := by
  classical
  obtain ⟨p, hp⟩ := lower.polygonal
  obtain ⟨q, hq⟩ := upper.polygonal
  refine ⟨insert m (p ∪ q), ?_⟩
  intro l hl r hr order noKnot t ht
  have midpoint : (1 - t) * l + t * r ∈ Set.Icc l r :=
    ⟨by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr order.le)],
      by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr order.le)]⟩
  by_cases first : r ≤ m
  · rw [splice_left (midpoint.2.trans first), splice_left (order.le.trans first), splice_left first]
    exact hp l ⟨hl.1, order.le.trans first⟩ r ⟨hr.1, first⟩ order
      (fun k hk => noKnot k (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left q hk)))) t ht
  · have last : m ≤ l := le_of_not_gt (fun ht' =>
      noKnot m (Finset.mem_insert_self _ _) ⟨ht', lt_of_not_ge first⟩)
    rw [splice_right contact (last.trans midpoint.1), splice_right contact last,
      splice_right contact (last.trans order.le)]
    exact hq l ⟨last, hl.2⟩ r ⟨last.trans order.le, hr.2⟩ order
      (fun k hk => noKnot k (Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right p hk)))) t ht

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
