module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarMotionDefs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarMotionLift

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v

namespace PolygonalCollar

variable {O : Type u} {W : ℕ} {cap : CollarSpec O W} (p q : PolygonalCollar cap)

/-- The union of the strand subdivisions in both collars, with the caps added. -/
noncomputable def commonHeights : Finset ℝ := Proofs.ProgressiveGluing.commonHeights p q

/-- A progressive frame with the same fixed ordered typed contacts at both caps. -/
noncomputable def blend (t : Time) : PolygonalCollar cap := Proofs.ProgressiveGluing.blend p q t

theorem blend_x (t : Time) (w : Fin W) (y : ℝ) :
    ((p.blend q t).wire w).x y = interpolate ((p.wire w).x y) ((q.wire w).x y) t.val := by rfl

theorem blend_zero : p.blend q ⟨0, le_rfl, zero_le_one⟩ = p :=
  Proofs.ProgressiveGluing.blend_zero p q

theorem blend_one : p.blend q ⟨1, zero_le_one, le_rfl⟩ = q :=
  Proofs.ProgressiveGluing.blend_one p q

/-- The same finite height subdivision works at every time, including both ends. -/
theorem blend_subdivides (t : Time) (w : Fin W) :
    Subdivides ((p.blend q t).wire w) (p.commonHeights q) :=
  Proofs.ProgressiveGluing.blend_subdivides p q t w

/-- Strict order at the endpoints of one common affine piece gives strict
order at every height in that piece. -/
theorem blend_segment_order (t : Time) (i j : Fin W) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a < b)
    (clear : ∀ k ∈ p.commonHeights q, k ∉ Set.Ioo a b)
    (left : ((p.blend q t).wire i).x a < ((p.blend q t).wire j).x a)
    (right : ((p.blend q t).wire i).x b < ((p.blend q t).wire j).x b)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((p.blend q t).wire i).x ((1 - s) * a + s * b) <
      ((p.blend q t).wire j).x ((1 - s) * a + s * b) :=
  Proofs.ProgressiveGluing.blend_segment_order p q t i j ha hb hab clear left right hs

/-- Continuity is joint in time and in the height along the strand. -/
theorem blend_continuous (w : Fin W) :
    Continuous (fun z : Time × Set.Icc (0 : ℝ) 1 => ((p.blend q z.1).wire w).point z.2.val) :=
  Proofs.ProgressiveGluing.continuous_blend p q w

end PolygonalCollar

namespace Diagram.OrderedVerticalMatch

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)

noncomputable def straightCollar : PolygonalCollar m.collarSpec :=
  Proofs.ProgressiveGluing.straightChoice m

theorem straightCollar_x (w : Fin (collarCount lower)) (y : ℝ) :
    (m.straightCollar.wire w).x y = interpolate (m.collarSpec.bottom w) (m.collarSpec.top w) y := by rfl

noncomputable def gluedWireCount : ℕ := Proofs.ProgressiveGluing.choiceWireCount m

/-- Two matched-cap attachments place the chosen collar between heights
1/4 and 1/2. -/
noncomputable def glueWith (p : PolygonalCollar m.collarSpec) :
    ProgressiveGraph.Diagram S (L + R) m.gluedWireCount .point :=
  Proofs.ProgressiveGluing.glueChoice m p

noncomputable def gluedLowerId (w : Fin A) : Fin m.gluedWireCount :=
  Proofs.ProgressiveGluing.choiceLowerId m w

noncomputable def gluedUpperId (w : Fin B) : Fin m.gluedWireCount :=
  Proofs.ProgressiveGluing.choiceUpperId m w

noncomputable def gluedCollarId (w : Fin (collarCount lower)) : Fin m.gluedWireCount :=
  Proofs.ProgressiveGluing.choiceCollarId m w

variable (p q : PolygonalCollar m.collarSpec)

theorem glueWith_x_lower (w : Fin A) {y : ℝ} (hy : y ≤ 1 / 4) :
    (m.glueWith p).x (m.gluedLowerId w) y = lower.x w (slabHeight 0 (slabHeight 0 y)) :=
  Proofs.ProgressiveGluing.glueChoice_lower m p w hy

theorem glueWith_x_upper (w : Fin B) {y : ℝ} (hy : 1 / 2 ≤ y) :
    (m.glueWith p).x (m.gluedUpperId w) y = upper.x w (slabHeight 1 y) :=
  Proofs.ProgressiveGluing.glueChoice_upper m p w hy

theorem glueWith_x_collar (w : Fin (collarCount lower)) {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (m.glueWith p).x (m.gluedCollarId w) y = (p.wire w).x (4 * y - 1) :=
  Proofs.ProgressiveGluing.glueChoice_collar m p w hy

/-- Changing the collar leaves vertex positions and labeled incidence fixed. -/
theorem glueWith_fixed_data :
    (m.glueWith p).vertexX = (m.glueWith q).vertexX ∧
    (m.glueWith p).vertexHeight = (m.glueWith q).vertexHeight ∧
    (m.glueWith p).generator = (m.glueWith q).generator ∧
    (m.glueWith p).label = (m.glueWith q).label ∧
    (m.glueWith p).start = (m.glueWith q).start ∧
    (m.glueWith p).finish = (m.glueWith q).finish ∧
    (∀ j, List.ofFn ((m.glueWith p).input j) = List.ofFn ((m.glueWith q).input j)) ∧
    (∀ j, List.ofFn ((m.glueWith p).output j) = List.ofFn ((m.glueWith q).output j)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- Every point of a strand outside the open collar slab stays fixed. This
includes the outer caps and both splice cuts. -/
theorem glueWith_fixed_outside (w : Fin m.gluedWireCount) {y : ℝ}
    (covered : (m.glueWith p).covers w y) (outside : y ≤ 1 / 4 ∨ 1 / 2 ≤ y) :
    (m.glueWith p).x w y = (m.glueWith q).x w y :=
  Proofs.ProgressiveGluing.glueChoice_fixed_outside m p q w covered outside

theorem glueWith_blend_zero : m.glueWith (p.blend q ⟨0, le_rfl, zero_le_one⟩) = m.glueWith p :=
  congrArg m.glueWith (p.blend_zero q)

theorem glueWith_blend_one : m.glueWith (p.blend q ⟨1, zero_le_one, le_rfl⟩) = m.glueWith q :=
  congrArg m.glueWith (p.blend_one q)

/-- A path of progressive drawings from the first gluing to the second.
Each frame is a pair of cap attachments, and the wire intervals are fixed. -/
theorem glueWith_blend_continuous (w : Fin m.gluedWireCount) :
    Continuous (fun z : PolygonalCollar.Time × {y : ℝ // (m.glueWith p).covers w y} =>
      ((m.glueWith (p.blend q z.1)).wire w).point z.2.val) :=
  Proofs.ProgressiveGluing.glueChoice_continuous m p q w

end Diagram.OrderedVerticalMatch
end Silmaril.RuntimeWires.ProgressiveGraph
