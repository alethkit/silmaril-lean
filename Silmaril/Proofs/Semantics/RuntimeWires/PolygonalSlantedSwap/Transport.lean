module

public import Silmaril.Proofs.Semantics.RuntimeWires.PolygonalSlantedSwap.Wires
public import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSlantedSwap

open Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor floor' : ℝ} {e f a : S.Edge}

private theorem rescale_input (h : BoxAltitude) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    BoxPair.rescale h (interpolate 0 1 u) = interpolate 0 h u := by
  simp only [interpolate, mul_zero, mul_one, zero_add]
  unfold BoxPair.rescale
  rw [min_eq_left hu.2, max_eq_right hu.2,
    min_eq_left (by norm_num : (1 : ℝ) ≤ 2),
    max_eq_right (show u - 2 ≤ 0 by linarith [hu.2])]
  ring

private theorem rescale_output (h : BoxAltitude) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    BoxPair.rescale h (interpolate 2 6 u) = interpolate (h.val + 1) 6 u := by
  have lo : 2 ≤ interpolate 2 6 u := by unfold interpolate; linarith [hu.1]
  have lo' : 1 ≤ interpolate 2 6 u := (by norm_num : (1 : ℝ) ≤ 2).trans lo
  unfold BoxPair.rescale
  rw [min_eq_right lo', max_eq_left lo', min_eq_right lo, max_eq_left (sub_nonneg.mpr lo)]
  unfold interpolate
  ring

variable (d : BoxPair S floor e f)

private theorem first_range : Set.Icc d.first.left d.first.right ⊆ Set.Icc d.leftSide d.rightSide := by
  rintro x ⟨hl, hr⟩
  exact ⟨(by unfold BoxPair.leftSide; linarith : d.leftSide ≤ d.first.left).trans hl,
    hr.trans (d.second.left_bound.le.trans (d.second.width.le.trans
      (by unfold BoxPair.rightSide; linarith)))⟩

private theorem second_range : Set.Icc d.second.left d.second.right ⊆ Set.Icc d.leftSide d.rightSide := by
  rintro x ⟨hl, hr⟩
  have h : d.leftSide ≤ d.first.left := by unfold BoxPair.leftSide; linarith
  exact ⟨h.trans (d.first.width.le.trans (d.second.left_bound.le.trans hl)),
    hr.trans (by unfold BoxPair.rightSide; linarith)⟩

theorem slanted_columns_disjoint (p : ExternalPorts d.first) (q : ExternalPorts d.second)
    (h k : BoxAltitude) : Disjoint (p.column h) (q.column k) := by
  rw [Set.disjoint_left]
  intro z hp hq
  exact (not_le_of_gt d.second.left_bound) ((column_bounds q k hq).1.1.trans
    (column_bounds p h hp).1.2)

theorem slanted_snapshot_inside (p : ExternalPorts d.first) (q : ExternalPorts d.second)
    (t : SwapTime) : d.slantedSnapshot p q t ⊆ d.rectangle := by
  intro z hz
  rcases hz with hz | hz
  · have h := column_bounds p _ hz
    exact ⟨first_range d h.1, h.2⟩
  · have h := column_bounds q _ hz
    exact ⟨second_range d h.1, h.2⟩

private theorem mapped_trace (t : SwapTime) {s : Slab} {r : Slab}
    (a : Strand s) (b : Strand r)
    (hmem : ∀ u ∈ Set.Icc (0 : ℝ) 1, a.point u ∈ d.rectangle)
    (hm : ∀ (u : ℝ) (hu : u ∈ Set.Icc 0 1),
      (d.deformation t ⟨a.point u, hmem u hu⟩).val = b.point u) :
    d.deformation t '' (Subtype.val ⁻¹' a.trace) = Subtype.val ⁻¹' b.trace := by
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, hwu⟩, rfl⟩
    have eq : (⟨a.point u, hmem u hu⟩ : d.rectangle) = w := Subtype.ext hwu
    exact ⟨u, hu, (hm u hu).symm.trans (congrArg (fun x => (d.deformation t x).val) eq)⟩
  · rintro ⟨u, hu, hzu⟩
    exact ⟨⟨a.point u, hmem u hu⟩, ⟨u, hu, rfl⟩, Subtype.ext ((hm u hu).trans hzu)⟩

variable {b : Box S floor' a} (p : ExternalPorts b)

private theorem incoming_image (t : SwapTime) (h k : BoxAltitude)
    (hr : Set.Icc b.left b.right ⊆ Set.Icc d.leftSide d.rightSide)
    (height : ∀ (z : d.rectangle), z.val.1 ∈ Set.Icc b.left b.right → ∀ {y : ℝ},
      z.val.2 = BoxPair.rescale h y → (d.deformation t z).val.2 = BoxPair.rescale k y)
    (i : Fin (S.source a).length) :
    d.deformation t '' (Subtype.val ⁻¹' (p.incoming h i).trace) =
      Subtype.val ⁻¹' (p.incoming k i).trace := by
  have inside (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
      (p.incoming h i).point u ∈ d.rectangle := by
    have hy := incoming_height p h i hu
    exact ⟨hr (incoming_horizontal p h i hu), hy.1, hy.2.trans (h.property.2.trans (by norm_num))⟩
  refine mapped_trace d t _ _ inside (fun u hu => Prod.ext ?_ ?_)
  · exact d.deformation_horizontal t _
  · calc
      _ = BoxPair.rescale k (interpolate 0 1 u) :=
        height _ (incoming_horizontal p h i hu) (rescale_input h hu).symm
      _ = _ := rescale_input k hu

private theorem outgoing_image (t : SwapTime) (h k : BoxAltitude)
    (hr : Set.Icc b.left b.right ⊆ Set.Icc d.leftSide d.rightSide)
    (height : ∀ (z : d.rectangle), z.val.1 ∈ Set.Icc b.left b.right → ∀ {y : ℝ},
      z.val.2 = BoxPair.rescale h y → (d.deformation t z).val.2 = BoxPair.rescale k y)
    (i : Fin (S.target a).length) :
    d.deformation t '' (Subtype.val ⁻¹' (p.outgoing h i).trace) =
      Subtype.val ⁻¹' (p.outgoing k i).trace := by
  have inside (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
      (p.outgoing h i).point u ∈ d.rectangle := by
    have hy := outgoing_height p h i hu
    exact ⟨hr (outgoing_horizontal p h i hu), by linarith [hy.1, h.property.1], hy.2⟩
  refine mapped_trace d t _ _ inside (fun u hu => Prod.ext ?_ ?_)
  · exact d.deformation_horizontal t _
  · calc
      _ = BoxPair.rescale k (interpolate 2 6 u) :=
        height _ (outgoing_horizontal p h i hu) (rescale_output h hu).symm
      _ = _ := rescale_output k hu

theorem slanted_first_cell (p : ExternalPorts d.first) (t : SwapTime) (c : BoxCell S e) :
    d.deformation t '' (Subtype.val ⁻¹' p.cell (BoxPair.firstAltitude swapStart) c) =
      Subtype.val ⁻¹' p.cell (BoxPair.firstAltitude t) c := by
  cases c with
  | body => exact d.first_cell_image t .body
  | input i =>
    exact incoming_image d p t _ _ (first_range d) (d.deformation_first_height t) i
  | output i =>
    exact outgoing_image d p t _ _ (first_range d) (d.deformation_first_height t) i

theorem slanted_second_cell (q : ExternalPorts d.second) (t : SwapTime) (c : BoxCell S f) :
    d.deformation t '' (Subtype.val ⁻¹' q.cell (BoxPair.secondAltitude swapStart) c) =
      Subtype.val ⁻¹' q.cell (BoxPair.secondAltitude t) c := by
  cases c with
  | body => exact d.second_cell_image t .body
  | input i =>
    exact incoming_image d q t _ _ (second_range d) (d.deformation_second_height t) i
  | output i =>
    exact outgoing_image d q t _ _ (second_range d) (d.deformation_second_height t) i

theorem slanted_snapshot_image (p : ExternalPorts d.first) (q : ExternalPorts d.second) (t : SwapTime) :
    d.deformation t '' (Subtype.val ⁻¹' d.slantedSnapshot p q swapStart) =
      Subtype.val ⁻¹' d.slantedSnapshot p q t := by
  simp only [BoxPair.slantedSnapshot, ExternalPorts.column, Set.preimage_union, Set.image_union,
    Set.preimage_iUnion, Set.image_iUnion, slanted_first_cell, slanted_second_cell]

end Silmaril.RuntimeWires.Proofs.PolygonalSlantedSwap
