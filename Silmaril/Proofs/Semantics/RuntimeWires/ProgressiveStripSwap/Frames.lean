module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveStripSwap.Wires
import all Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveStripSwap.Wires
import all Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveStripSwap.Ambient
import Mathlib.Tactic.NormNum

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : ProgressiveGraph.Diagram S V W .point}
variable (s : d.IsolatedStripSwap) (t : Time)

abbrev leftInside := (d.vertex_inside s.left).2
abbrev rightInside := (d.vertex_inside s.right).2
abbrev warp := regionMap (leftInside s) (rightInside s) t
abbrev plane := ambient s.strips (leftInside s) (rightInside s) t

def vertexHeight (v : Fin V) : ℝ := warp s t (s.vertexRegion v) (d.vertexHeight v)

private theorem lower_in_unit (w : Fin W) : 0 ≤ d.lower w := by
  cases h : d.start w with
  | none => exact (show 0 ≤ endpointHeight d.vertexHeight 0 (d.start w) by rw [h]; exact le_rfl)
  | some j => exact (show 0 ≤ endpointHeight d.vertexHeight 0 (d.start w) by rw [h]; exact (d.vertex_inside j).2.1.le)

private theorem upper_in_unit (w : Fin W) : d.upper w ≤ 1 := by
  cases h : d.finish w with
  | none => exact (show endpointHeight d.vertexHeight 1 (d.finish w) ≤ 1 by rw [h]; exact le_rfl)
  | some j => exact (show endpointHeight d.vertexHeight 1 (d.finish w) ≤ 1 by rw [h]; exact (d.vertex_inside j).2.2.le)

private theorem low_region (w : Fin W) (j : Fin V) (h : d.start w = some j) :
    s.wireRegion w = s.vertexRegion j := by
  have atEnd : d.covers w (d.lower w) := ⟨le_rfl, (d.wire w).increasing.le⟩
  have mem := s.wire_mem w (d.lower w) atEnd
  have hx : d.x w (d.lower w) = d.vertexX j := by
    unfold ProgressiveGraph.Diagram.lower
    rw [h]
    exact d.start_attached w j h
  rw [hx] at mem
  exact region_unique s.strips mem (s.vertex_mem j)

private theorem high_region (w : Fin W) (j : Fin V) (h : d.finish w = some j) :
    s.wireRegion w = s.vertexRegion j := by
  have atEnd : d.covers w (d.upper w) := ⟨(d.wire w).increasing.le, le_rfl⟩
  have mem := s.wire_mem w (d.upper w) atEnd
  have hx : d.x w (d.upper w) = d.vertexX j := by
    unfold ProgressiveGraph.Diagram.upper
    rw [h]
    exact d.finish_attached w j h
  rw [hx] at mem
  exact region_unique s.strips mem (s.vertex_mem j)

private theorem warp_strict (r : StripRegion) : StrictMono (warp s t r) :=
  region_increasing (leftInside s) (rightInside s) t r

private theorem warp_cap (r : StripRegion) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : warp s t r y = y :=
  region_caps (leftInside s) (rightInside s) t r h

private theorem unwarp_cap (r : StripRegion) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : (warp s t r).symm y = y := by
  nth_rewrite 1 [← warp_cap s t r h]
  exact (warp s t r).symm_apply_apply y

private theorem low_eq (w : Fin W) :
    endpointHeight (vertexHeight s t) 0 (d.start w) = warp s t (s.wireRegion w) (d.lower w) := by
  unfold ProgressiveGraph.Diagram.lower
  cases h : d.start w with
  | none => exact (warp_cap s t _ (Or.inl (le_refl 0))).symm
  | some j =>
    change warp s t (s.vertexRegion j) (d.vertexHeight j) = warp s t (s.wireRegion w) (d.vertexHeight j)
    rw [low_region s w j h]

private theorem high_eq (w : Fin W) :
    endpointHeight (vertexHeight s t) 1 (d.finish w) = warp s t (s.wireRegion w) (d.upper w) := by
  unfold ProgressiveGraph.Diagram.upper
  cases h : d.finish w with
  | none => exact (warp_cap s t _ (Or.inr (le_refl 1))).symm
  | some j =>
    change warp s t (s.vertexRegion j) (d.vertexHeight j) = warp s t (s.wireRegion w) (d.vertexHeight j)
    rw [high_region s w j h]

private abbrev movedWire (w : Fin W) :=
  moveWire (leftInside s) (rightInside s) t (s.wireRegion w) (d.wire w) (lower_in_unit w) (upper_in_unit w)

private def wire (w : Fin W) : Wire (endpointHeight (vertexHeight s t) 0 (d.start w))
    (endpointHeight (vertexHeight s t) 1 (d.finish w)) where
  x := (movedWire s t w).x
  increasing := by rw [low_eq, high_eq]; exact (movedWire s t w).increasing
  continuous := by rw [low_eq, high_eq]; exact (movedWire s t w).continuous
  polygonal := by rw [low_eq, high_eq]; exact (movedWire s t w).polygonal

private abbrev back (w : Fin W) (y : ℝ) := (warp s t (s.wireRegion w)).symm y

private theorem before {r : StripRegion} {x y : ℝ} (h : warp s t r x < y) : x < (warp s t r).symm y := by
  apply (warp_strict s t r).lt_iff_lt.mp
  rwa [Homeomorph.apply_symm_apply]

private theorem after {r : StripRegion} {x y : ℝ} (h : x < warp s t r y) : (warp s t r).symm x < y := by
  apply (warp_strict s t r).lt_iff_lt.mp
  rwa [Homeomorph.apply_symm_apply]

private theorem covers_back {w : Fin W} {y : ℝ}
    (h : y ∈ Set.Icc (endpointHeight (vertexHeight s t) 0 (d.start w))
      (endpointHeight (vertexHeight s t) 1 (d.finish w))) : d.covers w (back s t w y) := by
  rw [low_eq, high_eq] at h
  have inv := inverse_increasing (leftInside s) (rightInside s) t (s.wireRegion w)
  exact ⟨((warp s t _).symm_apply_apply _).symm.trans_le (inv.monotone h.1),
    (inv.monotone h.2).trans_eq ((warp s t _).symm_apply_apply _)⟩

private theorem crosses_back {w : Fin W} {y : ℝ}
    (h : y ∈ Set.Ioo (endpointHeight (vertexHeight s t) 0 (d.start w))
      (endpointHeight (vertexHeight s t) 1 (d.finish w))) : d.crosses w (back s t w y) := by
  rw [low_eq, high_eq] at h
  exact ⟨before s t h.1, after s t h.2⟩

private theorem plane_wire (w : Fin W) (y : ℝ) (hy : d.covers w y) :
    plane s t (d.x w y, y) = (d.x w y, warp s t (s.wireRegion w) y) :=
  ambient_region s.strips (leftInside s) (rightInside s) t (s.wireRegion w) _ (s.wire_mem w y hy)

theorem plane_vertex (j : Fin V) :
    plane s t (d.vertexX j, d.vertexHeight j) = (d.vertexX j, vertexHeight s t j) :=
  ambient_region s.strips (leftInside s) (rightInside s) t (s.vertexRegion j) _ (s.vertex_mem j)

/-- Each frame retains all of the original incidence data and ordered ports. -/
def drawing : ProgressiveGraph.Diagram S V W .point where
  vertexX := d.vertexX
  vertexHeight := vertexHeight s t
  vertex_inside j := by
    refine ⟨(d.vertex_inside j).1, ?_⟩
    have mono := warp_strict s t (s.vertexRegion j)
    refine ⟨(warp_cap s t _ (Or.inl (le_refl 0))).symm.trans_lt (mono (d.vertex_inside j).2.1),
      (mono (d.vertex_inside j).2.2).trans_eq (warp_cap s t _ (Or.inr (le_refl 1)))⟩
  vertex_separation := by
    intro j k same
    apply d.vertex_separation
    apply (plane s t).injective
    rw [plane_vertex, plane_vertex]
    exact same
  generator := d.generator
  label := d.label
  start := d.start
  finish := d.finish
  wire := wire s t
  wire_inside w y hy := d.wire_inside w _ (covers_back s t hy)
  start_attached w j h := by
    change d.x w (back s t w (vertexHeight s t j)) = d.vertexX j
    unfold back
    rw [vertexHeight, low_region s w j h, Homeomorph.symm_apply_apply]
    exact d.start_attached w j h
  finish_attached w j h := by
    change d.x w (back s t w (vertexHeight s t j)) = d.vertexX j
    unfold back
    rw [vertexHeight, high_region s w j h, Homeomorph.symm_apply_apply]
    exact d.finish_attached w j h
  separated := by
    intro w z ne y hw hz same
    have wc := crosses_back s t hw
    have zc := covers_back s t hz
    have image : plane s t (d.x w (back s t w y), back s t w y) =
        plane s t (d.x z (back s t z y), back s t z y) := by
      rw [plane_wire s t w _ ⟨wc.1.le, wc.2.le⟩, plane_wire s t z _ zc,
        Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      exact Prod.ext same rfl
    have old := (plane s t).injective image
    have sameHeight : back s t w y = back s t z y := congrArg Prod.snd old
    have sameX : d.x w (back s t w y) = d.x z (back s t z y) := congrArg Prod.fst old
    rw [← sameHeight] at sameX
    exact d.separated ne wc (sameHeight.symm ▸ zc) sameX
  avoids_vertex w j hy same := by
    let y := vertexHeight s t j
    change d.x w (back s t w y) = d.vertexX j at same
    have old := crosses_back s t hy
    have image : plane s t (d.x w (back s t w y), back s t w y) = plane s t (d.vertexX j, d.vertexHeight j) := by
      rw [plane_wire s t w _ ⟨old.1.le, old.2.le⟩, plane_vertex, Homeomorph.apply_symm_apply]
      exact Prod.ext same rfl
    have eq := (plane s t).injective image
    have sameHeight : back s t w y = d.vertexHeight j := congrArg Prod.snd eq
    have sameX : d.x w (back s t w y) = d.vertexX j := congrArg Prod.fst eq
    rw [sameHeight] at sameX
    exact d.avoids_vertex w j (sameHeight ▸ old) sameX
  input_boundary_separated := by
    intro w z ne hw hz
    change d.x w (back s t w 0) ≠ d.x z (back s t z 0)
    unfold back
    rw [unwarp_cap s t _ (Or.inl (le_refl 0)), unwarp_cap s t _ (Or.inl (le_refl 0))]
    exact d.input_boundary_separated ne hw hz
  output_boundary_separated := by
    intro w z ne hw hz
    change d.x w (back s t w 1) ≠ d.x z (back s t z 1)
    unfold back
    rw [unwarp_cap s t _ (Or.inr (le_refl 1)), unwarp_cap s t _ (Or.inr (le_refl 1))]
    exact d.output_boundary_separated ne hw hz
  input := d.input
  output := d.output
  input_exact := d.input_exact
  output_exact := d.output_exact
  input_types := d.input_types
  output_types := d.output_types
  input_order := by
    intro j i k less y hi hk hy
    have ri := high_region s (d.input j i) j ((d.input_exact j _).mpr ⟨i, rfl⟩)
    have rk := high_region s (d.input j k) j ((d.input_exact j _).mpr ⟨k, rfl⟩)
    change d.x (d.input j i) (back s t _ y) < d.x (d.input j k) (back s t _ y)
    change endpointHeight (vertexHeight s t) 0 (d.start (d.input j i)) < y at hi
    change endpointHeight (vertexHeight s t) 0 (d.start (d.input j k)) < y at hk
    rw [low_eq, ri] at hi
    rw [low_eq, rk] at hk
    unfold back
    rw [ri, rk]
    exact d.input_order j less (before s t hi) (before s t hk) (after s t hy)
  output_order := by
    intro j i k less y hy hi hk
    have ri := low_region s (d.output j i) j ((d.output_exact j _).mpr ⟨i, rfl⟩)
    have rk := low_region s (d.output j k) j ((d.output_exact j _).mpr ⟨k, rfl⟩)
    change d.x (d.output j i) (back s t _ y) < d.x (d.output j k) (back s t _ y)
    change y < endpointHeight (vertexHeight s t) 1 (d.finish (d.output j i)) at hi
    change y < endpointHeight (vertexHeight s t) 1 (d.finish (d.output j k)) at hk
    rw [high_eq, ri] at hi
    rw [high_eq, rk] at hk
    unfold back
    rw [ri, rk]
    exact d.output_order j less (before s t hy) (after s t hi) (after s t hk)

theorem wire_trace (w : Fin W) : plane s t '' (d.wire w).trace = ((drawing s t).wire w).trace := by
  ext point
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨warp s t (s.wireRegion w) y, ?_, ?_⟩
    · change _ ∈ Set.Icc (endpointHeight (vertexHeight s t) 0 (d.start w))
        (endpointHeight (vertexHeight s t) 1 (d.finish w))
      rw [low_eq, high_eq]
      exact ⟨(warp_strict s t _).monotone hy.1, (warp_strict s t _).monotone hy.2⟩
    · change (d.x w (back s t w (warp s t _ y)), warp s t _ y) = plane s t (d.x w y, y)
      rw [plane_wire s t w y hy]
      exact Prod.ext (congrArg (d.x w) ((warp s t _).symm_apply_apply y)) rfl
  · rintro ⟨y, hy, rfl⟩
    let z := back s t w y
    have old := covers_back s t hy
    refine ⟨(d.wire w).point z, ⟨z, old, rfl⟩, ?_⟩
    change plane s t (d.x w z, z) = (d.x w z, y)
    rw [plane_wire s t w z old]
    exact Prod.ext rfl ((warp s t _).apply_symm_apply y)

def isotopy : d.ProgressiveIsotopy where
  frame := plane s
  zero := ambient_zero s.strips (leftInside s) (rightInside s)
  continuous_frame := ambient_continuous s.strips (leftInside s) (rightInside s)
  continuous_inverse := ambient_continuous_inv s.strips (leftInside s) (rightInside s)
  caps := ambient_caps s.strips (leftInside s) (rightInside s)
  drawing := drawing s
  generator _ := rfl
  label _ := rfl
  start _ := rfl
  finish _ := rfl
  inputs _ _ := rfl
  outputs _ _ := rfl
  trace := wire_trace s
  vertex := plane_vertex s

theorem left_height : (drawing s t).vertexHeight s.left =
    interpolate (d.vertexHeight s.left) (d.vertexHeight s.right) t.val := by
  change warp s t (s.vertexRegion s.left) (d.vertexHeight s.left) = _
  rw [s.left_region]
  exact heightMap_middle (leftInside s) (lerp_inside (leftInside s) (rightInside s) t)

theorem right_height : (drawing s t).vertexHeight s.right =
    interpolate (d.vertexHeight s.right) (d.vertexHeight s.left) t.val := by
  change warp s t (s.vertexRegion s.right) (d.vertexHeight s.right) = _
  rw [s.right_region]
  exact heightMap_middle (rightInside s) (lerp_inside (rightInside s) (leftInside s) t)

theorem fixed_exterior (z : ℝ × ℝ) (hz : z.1 ∈ s.strips.region .exterior) : plane s t z = z :=
  ambient_region s.strips (leftInside s) (rightInside s) t .exterior z hz

theorem exterior_wire (w : Fin W) (h : s.wireRegion w = .exterior) :
    ((drawing s t).wire w).trace = (d.wire w).trace := by
  have fixed (z : ℝ × ℝ) (hz : z ∈ (d.wire w).trace) : plane s t z = z := by
    obtain ⟨y, hy, rfl⟩ := hz
    have mem := s.wire_mem w y hy
    rw [h] at mem
    exact fixed_exterior s t _ mem
  rw [← wire_trace s t w]
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [fixed q hq]
  · intro hz
    exact ⟨z, hz, fixed z hz⟩

theorem cap_x (w : Fin W) (y : ℝ) (hy : y ≤ 0 ∨ 1 ≤ y) :
    (drawing s t).x w y = d.x w y := by
  change d.x w (back s t w y) = _
  unfold back
  rw [unwarp_cap s t _ hy]

/-- Recover the original ordered cap enumerations in every frame. -/
def fixedDrawingAt {a b : CapProfile O} (p : FixedDrawing S a b)
    (s : p.drawing.IsolatedStripSwap) (t : Time) : FixedDrawing S a b where
  vertices := p.vertices
  wires := p.wires
  drawing := drawing s t
  input := p.input
  output := p.output
  input_label := p.input_label
  output_label := p.output_label
  input_x i := (cap_x s t _ 0 (Or.inl (le_refl 0))).trans (p.input_x i)
  output_x i := (cap_x s t _ 1 (Or.inr (le_refl 1))).trans (p.output_x i)

end Silmaril.RuntimeWires.Proofs.ProgressiveStripSwap
