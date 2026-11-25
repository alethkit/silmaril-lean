module

public import Silmaril.Proofs.Semantics.RuntimeWires.PolygonalSwap.Ambient
import Silmaril.Semantics.RuntimeWires.Polygonal.Thms
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSwap

open Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor floor' : ℝ} {e f a : S.Edge}

private theorem mem_positions {A : List O} (p : Frontier A) (x : ℝ) :
    x ∈ p.positions ↔ ∃ i : Fin A.length, p.coordinate i = x := by
  constructor
  · intro h
    obtain ⟨i, ei⟩ := List.mem_iff_get.mp h
    exact ⟨Fin.cast p.length_eq i, by simpa [Frontier.coordinate] using ei⟩
  · rintro ⟨i, rfl⟩
    exact List.get_mem ..

private theorem vertical_trace (slab : Slab) (x : ℝ) :
    (Strand.mk (slab := slab) x x).trace = {x} ×ˢ Set.Icc slab.lower slab.upper := by
  let s : Strand slab := ⟨x, x⟩
  have xval (t : ℝ) : (s.point t).1 = x := by
    change interpolate x x t = x
    unfold interpolate
    ring
  have y0 : (s.point 0).2 = slab.lower := by simp [Strand.point, interpolate]
  have y1 : (s.point 1).2 = slab.upper := by simp [Strand.point, interpolate]
  ext p
  change p ∈ s.trace ↔ p ∈ {x} ×ˢ Set.Icc slab.lower slab.upper
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨xval t, y0 ▸ s.strictHeight.monotone ht.1, y1 ▸ s.strictHeight.monotone ht.2⟩
  · rintro ⟨hx, hy⟩
    have hc : Continuous (fun t => (s.point t).2) := by
      change Continuous (interpolate slab.lower slab.upper)
      unfold interpolate
      fun_prop
    have hrange := hc.continuousOn.surjOn_Icc (s := Set.Icc (0 : ℝ) 1)
      (show 0 ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
      (show 1 ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    rw [y0, y1] at hrange
    obtain ⟨t, ht, hyt⟩ := hrange hy
    exact ⟨t, ht, Prod.ext ((xval t).trans (Set.mem_singleton_iff.mp hx).symm) hyt⟩

private def cellWidth (b : Box S floor' a) : BoxCell S a → Set ℝ
  | .body => Set.Icc b.left b.right
  | .input i => {b.input.coordinate i}
  | .output i => {b.output.coordinate i}

private def cellSlab (h : BoxAltitude) : BoxCell S a → Slab
  | .body => BoxAltitude.body h
  | .input _ => BoxAltitude.inputs h
  | .output _ => BoxAltitude.outputs h

private theorem cell_product (b : Box S floor' a) (h : BoxAltitude) (c : BoxCell S a) :
    b.cell h c = cellWidth b c ×ˢ Set.Icc (cellSlab h c).lower (cellSlab h c).upper := by
  cases c with
  | body => rfl
  | input i => exact vertical_trace _ _
  | output i => exact vertical_trace _ _

private theorem width_inside (b : Box S floor' a) (c : BoxCell S a) :
    cellWidth b c ⊆ Set.Icc b.left b.right := by
  intro x hx
  cases c with
  | body => exact hx
  | input i =>
    have h := b.input_inside x ((mem_positions _ _).mpr ⟨i, (Set.mem_singleton_iff.mp hx).symm⟩)
    exact ⟨h.1.le, h.2.le⟩
  | output i =>
    have h := b.output_inside x ((mem_positions _ _).mpr ⟨i, (Set.mem_singleton_iff.mp hx).symm⟩)
    exact ⟨h.1.le, h.2.le⟩

private theorem slab_inside (h : BoxAltitude) (c : BoxCell S a) :
    Set.Icc (cellSlab h c).lower (cellSlab h c).upper ⊆ Set.Icc 0 6 := by
  rintro y ⟨hy₁, hy₂⟩
  cases c with
  | body =>
    change h.val ≤ y at hy₁
    change y ≤ h.val + 1 at hy₂
    exact ⟨by linarith [h.property.1], by linarith [h.property.2]⟩
  | input i =>
    change 0 ≤ y at hy₁
    change y ≤ h.val at hy₂
    exact ⟨hy₁, by linarith [h.property.2]⟩
  | output i =>
    change h.val + 1 ≤ y at hy₁
    change y ≤ 6 at hy₂
    exact ⟨by linarith [h.property.1], hy₂⟩

private theorem cell_horizontal (b : Box S floor' a) (h : BoxAltitude) (c : BoxCell S a)
    {p : Point} (hp : p ∈ b.cell h c) : p.1 ∈ Set.Icc b.left b.right := by
  rw [cell_product] at hp
  exact width_inside b c hp.1

private theorem cell_inside {d : BoxPair S floor e f} (b : Box S floor' a) (h : BoxAltitude)
    (c : BoxCell S a) (hl : d.leftSide ≤ b.left) (hr : b.right ≤ d.rightSide) :
    b.cell h c ⊆ d.rectangle := by
  intro p hp
  have hx := cell_horizontal b h c hp
  rw [cell_product] at hp
  exact ⟨⟨hl.trans hx.1, hx.2.trans hr⟩, slab_inside h c hp.2⟩

theorem columns_disjoint (d : BoxPair S floor e f) (h k : BoxAltitude) :
    Disjoint (d.first.column h) (d.second.column k) := by
  rw [Set.disjoint_left]
  intro p hp hq
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
  obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hq
  exact not_lt_of_ge ((cell_horizontal d.second k c' hc').1.trans
    (cell_horizontal d.first h c hc).2) d.second.left_bound

theorem incoming_contact (b : Box S floor' a) (h : BoxAltitude) (i : Fin (S.source a).length) :
    (b.incoming h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.input.coordinate i, h.val)} := by
  have hi := width_inside b (.input i) (show b.input.coordinate i ∈ cellWidth b (.input i) from rfl)
  change b.cell h (.input i) ∩ b.cell h .body = _
  rw [cell_product, cell_product]
  ext p
  change (p.1 = b.input.coordinate i ∧ (0 ≤ p.2 ∧ p.2 ≤ h.val)) ∧
    (p.1 ∈ Set.Icc b.left b.right ∧ (h.val ≤ p.2 ∧ p.2 ≤ h.val + 1)) ↔ _
  constructor
  · rintro ⟨⟨hx, _, ht⟩, _, hb, _⟩
    exact Prod.ext hx (le_antisymm ht hb)
  · rintro rfl
    exact ⟨⟨rfl, zero_lt_one.le.trans h.property.1, le_rfl⟩,
      hi, le_rfl, le_add_of_nonneg_right zero_le_one⟩

theorem outgoing_contact (b : Box S floor' a) (h : BoxAltitude) (i : Fin (S.target a).length) :
    (b.outgoing h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.output.coordinate i, h.val + 1)} := by
  have hi := width_inside b (.output i) (show b.output.coordinate i ∈ cellWidth b (.output i) from rfl)
  change b.cell h (.output i) ∩ b.cell h .body = _
  rw [cell_product, cell_product]
  ext p
  change (p.1 = b.output.coordinate i ∧ (h.val + 1 ≤ p.2 ∧ p.2 ≤ 6)) ∧
    (p.1 ∈ Set.Icc b.left b.right ∧ (h.val ≤ p.2 ∧ p.2 ≤ h.val + 1)) ↔ _
  constructor
  · rintro ⟨⟨hx, hb, _⟩, _, _, ht⟩
    exact Prod.ext hx (le_antisymm ht hb)
  · rintro rfl
    exact ⟨⟨rfl, le_rfl, by linarith [h.property.2]⟩,
      hi, le_add_of_nonneg_right zero_le_one, le_rfl⟩

theorem input_output_disjoint (b : Box S floor' a) (h : BoxAltitude)
    (i : Fin (S.source a).length) (j : Fin (S.target a).length) :
    Disjoint (b.incoming h i).trace (b.outgoing h j).trace := by
  change Disjoint (b.cell h (.input i)) (b.cell h (.output j))
  rw [cell_product, cell_product, Set.disjoint_left]
  rintro p ⟨_, ⟨_, hi⟩⟩ ⟨_, ⟨ho, _⟩⟩
  change p.2 ≤ h.val at hi
  change h.val + 1 ≤ p.2 at ho
  linarith

variable (d : BoxPair S floor e f)

private theorem frame_product (t : SwapTime) {X : Set ℝ} {h : BoxAltitude} {low high : ℝ}
    (ha : ∀ x ∈ X, d.altitude t x = h.val) (horder : low ≤ high) :
    d.frame t '' (X ×ˢ Set.Icc low high) =
      X ×ˢ Set.Icc (BoxPair.rescale h low) (BoxPair.rescale h high) := by
  have hr := rescale_image h.property horder
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hq.1, ?_⟩
    change BoxPair.rescale (d.altitude t q.1) q.2 ∈ _
    rw [ha q.1 hq.1, ← hr]
    exact ⟨q.2, hq.2, rfl⟩
  · rintro ⟨hx, hy⟩
    rw [← hr] at hy
    obtain ⟨y, hy, ey⟩ := hy
    refine ⟨(p.1, y), ⟨hx, hy⟩, Prod.ext (by rfl) ?_⟩
    change BoxPair.rescale (d.altitude t p.1) y = p.2
    rw [ha p.1 hx, ey]

private theorem frame_cell (t : SwapTime) (b : Box S floor' a) (h : BoxAltitude)
    (ha : ∀ x ∈ Set.Icc b.left b.right, d.altitude t x = h.val) (c : BoxCell S a) :
    d.frame t '' b.cell referenceAltitude c = b.cell h c := by
  rw [cell_product, cell_product,
    frame_product d t (fun x hx => ha x (width_inside b c hx)) (cellSlab referenceAltitude c).increasing.le]
  cases c <;>
    simp [cellSlab, BoxAltitude.body, BoxAltitude.inputs, BoxAltitude.outputs, Slab.unit,
      referenceAltitude, show (1 : ℝ) + 1 = 2 by norm_num,
      rescale_zero, rescale_one, rescale_two, rescale_six]

private theorem frameHomeomorph_cell (t : SwapTime) (b : Box S floor' a) (h : BoxAltitude)
    (hl : d.leftSide ≤ b.left) (hr : b.right ≤ d.rightSide)
    (ha : ∀ x ∈ Set.Icc b.left b.right, d.altitude t x = h.val) (c : BoxCell S a) :
    frameHomeomorph d t '' (Subtype.val ⁻¹' b.cell referenceAltitude c) =
      Subtype.val ⁻¹' b.cell h c := by
  have image := frame_cell d t b h ha c
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change (frameHomeomorph d t q).val ∈ b.cell h c
    rw [frameHomeomorph_val, ← image]
    exact ⟨q.val, hq, rfl⟩
  · intro hp
    change p.val ∈ b.cell h c at hp
    rw [← image] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    refine ⟨⟨q, cell_inside b referenceAltitude c hl hr hq⟩, hq, Subtype.ext ?_⟩
    rw [frameHomeomorph_val]
    exact hqp

private theorem deformation_cell {X Y Z : Set d.rectangle} (t : SwapTime)
    (h0 : frameHomeomorph d swapStart '' X = Y) (ht : frameHomeomorph d t '' X = Z) :
    deformation d t '' Y = Z := by
  have h : (frameHomeomorph d swapStart).symm '' Y = X := by
    rw [← h0, ← Set.image_comp]
    simp
  have eq : ⇑(deformation d t) = frameHomeomorph d t ∘ (frameHomeomorph d swapStart).symm :=
    funext (deformation_apply d t)
  rw [eq, Set.image_comp, h, ht]

private theorem sides : d.leftSide < d.first.left ∧ d.second.right < d.rightSide := by
  simp only [BoxPair.leftSide, BoxPair.rightSide]
  constructor <;> linarith

theorem snapshot_inside (t : SwapTime) : d.snapshot t ⊆ d.rectangle := by
  intro p hp
  rcases hp with hp | hp
  · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
    exact cell_inside d.first _ c (sides d).1.le
      (d.second.left_bound.le.trans (d.second.width.le.trans (sides d).2.le)) hc
  · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
    exact cell_inside d.second _ c
      ((sides d).1.le.trans (d.first.width.le.trans d.second.left_bound.le)) (sides d).2.le hc

theorem first_cell (t : SwapTime) (c : BoxCell S e) :
    deformation d t '' (Subtype.val ⁻¹' d.first.cell (BoxPair.firstAltitude swapStart) c) =
      Subtype.val ⁻¹' d.first.cell (BoxPair.firstAltitude t) c := by
  have hl := (sides d).1.le
  have hr := d.second.left_bound.le.trans (d.second.width.le.trans (sides d).2.le)
  exact deformation_cell d t
    (frameHomeomorph_cell d swapStart d.first _ hl hr (fun _ => altitude_first d swapStart) c)
    (frameHomeomorph_cell d t d.first _ hl hr (fun _ => altitude_first d t) c)

theorem second_cell (t : SwapTime) (c : BoxCell S f) :
    deformation d t '' (Subtype.val ⁻¹' d.second.cell (BoxPair.secondAltitude swapStart) c) =
      Subtype.val ⁻¹' d.second.cell (BoxPair.secondAltitude t) c := by
  have hl := (sides d).1.le.trans (d.first.width.le.trans d.second.left_bound.le)
  have hr := (sides d).2.le
  exact deformation_cell d t
    (frameHomeomorph_cell d swapStart d.second _ hl hr (fun _ => altitude_second d swapStart) c)
    (frameHomeomorph_cell d t d.second _ hl hr (fun _ => altitude_second d t) c)

theorem snapshot_image (t : SwapTime) :
    deformation d t '' (Subtype.val ⁻¹' d.snapshot swapStart) = Subtype.val ⁻¹' d.snapshot t := by
  simp only [BoxPair.snapshot, Box.column, Set.preimage_union, Set.image_union,
    Set.preimage_iUnion, Set.image_iUnion, first_cell, second_cell]

private theorem cut_after (b : Box S floor' a) (h : BoxAltitude) (p : Point)
    (hcut : h.val + 1 < p.2) (hhi : p.2 ≤ 6) :
    p ∈ b.column h ↔ p.1 ∈ b.output.positions := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
    rw [cell_product] at hc
    cases c with
    | body => exact (not_le_of_gt hcut hc.2.2).elim
    | input i =>
      have ht : p.2 ≤ h.val := hc.2.2
      exact (by linarith : False).elim
    | output i => exact (mem_positions _ _).mpr ⟨i, hc.1.symm⟩
  · intro hp
    obtain ⟨i, hi⟩ := (mem_positions _ _).mp hp
    refine Set.mem_iUnion.mpr ⟨.output i, ?_⟩
    rw [cell_product]
    exact ⟨hi.symm, hcut.le, hhi⟩

private theorem cut_before (b : Box S floor' a) (h : BoxAltitude) (p : Point)
    (hlo : 0 ≤ p.2) (hcut : p.2 < h.val) :
    p ∈ b.column h ↔ p.1 ∈ b.input.positions := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
    rw [cell_product] at hc
    cases c with
    | body => exact (not_le_of_gt hcut hc.2.1).elim
    | input i => exact (mem_positions _ _).mpr ⟨i, hc.1.symm⟩
    | output i =>
      have ht : h.val + 1 ≤ p.2 := hc.2.1
      exact (by linarith : False).elim
  · intro hp
    obtain ⟨i, hi⟩ := (mem_positions _ _).mp hp
    refine Set.mem_iUnion.mpr ⟨.input i, ?_⟩
    rw [cell_product]
    exact ⟨hi.symm, hlo, hcut.le⟩

theorem first_cut :
    d.snapshot swapStart ∩ {p | p.2 = 3} = {p | p.1 ∈ d.firstSeam.positions ∧ p.2 = 3} := by
  ext p
  change ((_ ∨ _) ∧ p.2 = 3) ↔ (p.1 ∈ d.first.output.positions ++ d.second.input.positions ∧ p.2 = 3)
  rw [List.mem_append]
  refine and_congr_left (fun hp => or_congr ?_ ?_)
  · apply cut_after
    · rw [hp]; norm_num [BoxPair.firstAltitude, swapStart]
    · rw [hp]; norm_num
  · apply cut_before
    · rw [hp]; norm_num
    · rw [hp]; norm_num [BoxPair.secondAltitude, swapStart]

theorem second_cut :
    d.snapshot swapFinish ∩ {p | p.2 = 3} = {p | p.1 ∈ d.secondSeam.positions ∧ p.2 = 3} := by
  ext p
  change ((_ ∨ _) ∧ p.2 = 3) ↔ (p.1 ∈ d.first.input.positions ++ d.second.output.positions ∧ p.2 = 3)
  rw [List.mem_append]
  refine and_congr_left (fun hp => or_congr ?_ ?_)
  · apply cut_before
    · rw [hp]; norm_num
    · rw [hp]; norm_num [BoxPair.firstAltitude, swapFinish]
  · apply cut_after
    · rw [hp]; norm_num [BoxPair.secondAltitude, swapFinish]
    · rw [hp]; norm_num

open Silmaril.RuntimeWires.Sliced

theorem schedule_swap (e f : S.Edge) :
    Sheet.SeamEquivalent (BoxPair.firstThenSecond S e f) (BoxPair.secondThenFirst S e f) := by
  let parallel := Sheet.cons (S := S) (.box e (.box f .empty)) (.empty _)
  have first : Sheet.Move S parallel (BoxPair.firstThenSecond S e f) :=
    .split (.upper e (.lower f .empty)) _
  have second : Sheet.Move S parallel (BoxPair.secondThenFirst S e f) :=
    .split (.lower e (.upper f .empty)) _
  exact .trans _ _ _ (.symm _ _ (.rel _ _ first)) (.rel _ _ second)

end Silmaril.RuntimeWires.Proofs.PolygonalSwap
