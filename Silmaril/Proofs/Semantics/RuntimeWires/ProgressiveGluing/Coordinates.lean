module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Wire
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
section Vertices

variable {U : ℕ} {lower : Diagram S L W .point} {upper : Diagram S R U .point}

theorem x_left (v : Fin L) : gluedVertexX lower upper (Fin.castAdd R v) = lower.vertexX v := by
  simp [gluedVertexX]

theorem x_right (v : Fin R) : gluedVertexX lower upper (Fin.natAdd L v) = upper.vertexX v := by
  simp [gluedVertexX]

theorem height_left (v : Fin L) :
    gluedHeight lower upper (Fin.castAdd R v) = halfHeight 0 (lower.vertexHeight v) := by
  simp [gluedHeight]

theorem height_right (v : Fin R) :
    gluedHeight lower upper (Fin.natAdd L v) = halfHeight 1 (upper.vertexHeight v) := by
  simp [gluedHeight]

end Vertices

variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

theorem low_bound (w : Fin W) :
    endpointHeight (gluedHeight lower upper) 0 (gluedStart lower (R := R) w) =
      halfHeight 0 (lower.lower w) := by
  cases h : lower.start w with
  | none => norm_num [gluedStart, Diagram.lower, endpointHeight, h, halfHeight]
  | some v => simp [gluedStart, Diagram.lower, endpointHeight, h, height_left]

theorem high_bound (w : Fin W) :
    endpointHeight (gluedHeight lower upper) 1 (gluedFinish (L := L) upper w) =
      halfHeight 1 (upper.upper w) := by
  cases h : upper.finish w with
  | none => norm_num [gluedFinish, Diagram.upper, endpointHeight, h, halfHeight]
  | some v => simp [gluedFinish, Diagram.upper, endpointHeight, h, height_right]

include m in
theorem lower_cap_height (w : Fin W) : lower.upper w = 1 := by
  simp [Diagram.upper, endpointHeight, m.lower_cap w]

include m in
theorem upper_cap_height (w : Fin W) : upper.lower w = 0 := by
  simp [Diagram.lower, endpointHeight, m.upper_cap w]

include m in
theorem lower_end (w : Fin W) : lower.lower w < 1 :=
  lower_cap_height m w ▸ (lower.wire w).increasing

include m in
theorem upper_end (w : Fin W) : 0 < upper.upper w :=
  upper_cap_height m w ▸ (upper.wire w).increasing

theorem lower_inside (v : Fin L) :
    halfHeight 0 (lower.vertexHeight v) ∈ Set.Ioo 0 (1 / 2 : ℝ) := by
  have original := (lower.vertex_inside v).2
  exact ⟨by dsimp only [halfHeight]; linarith [original.1], by dsimp only [halfHeight]; linarith [original.2]⟩

theorem upper_inside (v : Fin R) :
    halfHeight 1 (upper.vertexHeight v) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have original := (upper.vertex_inside v).2
  exact ⟨by dsimp only [halfHeight]; linarith [original.1], by dsimp only [halfHeight]; linarith [original.2]⟩

include m in
theorem below_join (w : Fin W) : halfHeight 0 (lower.lower w) < (1 / 2 : ℝ) := by
  dsimp only [halfHeight]
  linarith [lower_end m w]

include m in
theorem above_join (w : Fin W) : (1 / 2 : ℝ) < halfHeight 1 (upper.upper w) := by
  dsimp only [halfHeight]
  linarith [upper_end m w]

noncomputable def lowerHalf (w : Fin W) : Wire (halfHeight 0 (lower.lower w)) (1 / 2) :=
  ((lower.wire w).halve 0).atBounds rfl (by
    change halfHeight 0 (lower.upper w) = _
    rw [lower_cap_height m w]
    norm_num [halfHeight])

noncomputable def upperHalf (w : Fin W) : Wire (1 / 2) (halfHeight 1 (upper.upper w)) :=
  ((upper.wire w).halve 1).atBounds (by
    change halfHeight 1 (upper.lower w) = _
    rw [upper_cap_height m w]
    norm_num [halfHeight]) rfl

theorem joined_contact (w : Fin W) : (lowerHalf m w).x (1 / 2) = (upperHalf m w).x (1 / 2) := by
  change lower.x w (slabHeight 0 (1 / 2)) = upper.x w (slabHeight 1 (1 / 2))
  simpa [slabHeight] using m.coordinate w

noncomputable def gluedWire (w : Fin W) :
    Wire (endpointHeight (gluedHeight lower upper) 0 (gluedStart lower (R := R) w))
      (endpointHeight (gluedHeight lower upper) 1 (gluedFinish (L := L) upper w)) :=
  ((lowerHalf m w).splice (upperHalf m w) (joined_contact m w)).atBounds
    (low_bound w).symm (high_bound w).symm

theorem wire_left (w : Fin W) {y : ℝ} (h : y ≤ 1 / 2) :
    (gluedWire m w).x y = lower.x w (slabHeight 0 y) :=
  (lowerHalf m w).splice_x_lower (upperHalf m w) (joined_contact m w) h

theorem wire_right (w : Fin W) {y : ℝ} (h : 1 / 2 ≤ y) :
    (gluedWire m w).x y = upper.x w (slabHeight 1 y) :=
  (lowerHalf m w).splice_x_upper (upperHalf m w) (joined_contact m w) h

theorem unscale (offset y : ℝ) : slabHeight offset (halfHeight offset y) = y := by
  unfold slabHeight halfHeight
  linarith

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
