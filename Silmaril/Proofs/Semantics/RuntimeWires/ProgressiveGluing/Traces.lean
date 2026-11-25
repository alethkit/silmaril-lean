module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Geometry
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Drawing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

private theorem half_of_slab (offset y : ℝ) : halfHeight offset (slabHeight offset y) = y := by
  unfold halfHeight slabHeight
  linarith

/-- The trace of a spliced wire is exactly the two rescaled traces. -/
theorem glue_trace (w : Fin W) :
    (m.glue.wire w).trace =
      (fun p : ℝ × ℝ => (p.1, halfHeight 0 p.2)) '' (lower.wire w).trace ∪
      (fun p : ℝ × ℝ => (p.1, halfHeight 1 p.2)) '' (upper.wire w).trace := by
  have lowEq : jointLower lower upper w = m.glue.lower w :=
    (low_bound (upper := upper) w).trans (m.glue_lower w).symm
  have highEq : jointUpper lower upper w = m.glue.upper w :=
    (high_bound (lower := lower) w).trans (m.glue_upper w).symm
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases le_total y (1 / 2 : ℝ) with lo | hi
    · refine Or.inl ⟨(lower.wire w).point (slabHeight 0 y), ⟨_, left_covered m lo (by rw [lowEq]; exact hy.1), rfl⟩, ?_⟩
      exact Prod.ext (m.glue_x_below w lo).symm (half_of_slab 0 y)
    · refine Or.inr ⟨(upper.wire w).point (slabHeight 1 y), ⟨_, right_covered m hi (by rw [highEq]; exact hy.2), rfl⟩, ?_⟩
      exact Prod.ext (m.glue_x_above w hi).symm (half_of_slab 1 y)
  · rintro (⟨p, ⟨h, hw, rfl⟩, rfl⟩ | ⟨p, ⟨h, hw, rfl⟩, rfl⟩)
    · have hw' : h ∈ Set.Icc (lower.lower w) (lower.upper w) := hw
      have h1 : h ≤ 1 := (lower_cap_height m w) ▸ hw'.2
      have hi : halfHeight 0 h ≤ 1 / 2 := by
        simpa only [show halfHeight 0 1 = 1 / 2 by norm_num [halfHeight]] using
          (halfHeight_strictMono 0).monotone h1
      have lo : m.glue.lower w ≤ halfHeight 0 h := by
        rw [m.glue_lower]
        exact (halfHeight_strictMono 0).monotone hw'.1
      refine ⟨halfHeight 0 h, ⟨lo, hi.trans (m.crosses_join w).2.le⟩, Prod.ext ?_ rfl⟩
      change m.glue.x w (halfHeight 0 h) = lower.x w h
      rw [m.glue_x_below w hi, unscale]
    · have hw' : h ∈ Set.Icc (upper.lower w) (upper.upper w) := hw
      have h0 : 0 ≤ h := (upper_cap_height m w) ▸ hw'.1
      have lo : 1 / 2 ≤ halfHeight 1 h := by
        simpa only [show halfHeight 1 0 = 1 / 2 by norm_num [halfHeight]] using
          (halfHeight_strictMono 1).monotone h0
      have hi : halfHeight 1 h ≤ m.glue.upper w := by
        rw [m.glue_upper]
        exact (halfHeight_strictMono 1).monotone hw'.2
      refine ⟨halfHeight 1 h, ⟨(m.crosses_join w).1.le.trans lo, hi⟩, Prod.ext ?_ rfl⟩
      change m.glue.x w (halfHeight 1 h) = upper.x w h
      rw [m.glue_x_above w lo, unscale]

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
