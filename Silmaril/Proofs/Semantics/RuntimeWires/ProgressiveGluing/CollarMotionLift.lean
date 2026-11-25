module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarMotionJoins
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.PartialGluing
open OrderedVerticalMatch (collarIndex collarCount)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)
variable (p q : PolygonalCollar m.collarSpec) (t : PolygonalCollar.Time)

private theorem assemble_x_lower {X Y C D : ℕ}
    {d : ProgressiveGraph.Diagram S X C .point} {e : ProgressiveGraph.Diagram S Y D .point}
    (j : d.PartialVerticalMatch e) (w : Fin C) {y : ℝ} (hy : y ≤ 1 / 2) :
    (assemble j).x (lowerId (lower := d) (upper := e) w) y = d.x w (slabHeight 0 y) := by
  change jointX j ((numbering d e).symm ((numbering d e) (fromLower w))) y = _
  rw [Equiv.symm_apply_apply]
  exact x_fromLower j w hy

private theorem assemble_x_upper {X Y C D : ℕ}
    {d : ProgressiveGraph.Diagram S X C .point} {e : ProgressiveGraph.Diagram S Y D .point}
    (j : d.PartialVerticalMatch e) (w : Fin D) {y : ℝ} (hy : 1 / 2 ≤ y) :
    (assemble j).x (j.upperId w) y = e.x w (slabHeight 1 y) := by
  change jointX j ((numbering d e).symm ((numbering d e) (j.fromUpper w))) y = _
  rw [Equiv.symm_apply_apply]
  exact x_fromUpper j w hy

private theorem lowerAttached_blend (w : Fin (wireCount lower (polygonalDrawing (S := S) p))) (y : ℝ) :
    (lowerAttached m (blend p q t)).x w y =
      interpolate ((lowerAttached m p).x w y) ((lowerAttached m q).x w y) t.val := by
  let e := numbering lower (polygonalDrawing (S := S) p)
  change jointX (lowerChoice m (blend p q t)) (e.symm w) y =
    interpolate (jointX (lowerChoice m p) (e.symm w) y) (jointX (lowerChoice m q) (e.symm w) y) t.val
  rcases e.symm w with w | (w | w)
  · exact (interpolate_id _ _).symm
  · by_cases h : y ≤ 1 / 2
    · simp only [jointX, jointWire, Wire.atBounds, Wire.splice, spliceX, ite_eq_left h]
      exact (interpolate_id _ _).symm
    · simp only [jointX, jointWire, Wire.atBounds, Wire.splice, spliceX, ite_eq_right h]
      rfl
  · exact (w.property rfl).elim

theorem glueChoice_blend (w : Fin (choiceWireCount m)) (y : ℝ) :
    (glueChoice m (blend p q t)).x w y =
      interpolate ((glueChoice m p).x w y) ((glueChoice m q).x w y) t.val := by
  let e := numbering (lowerAttached m p) upper
  change jointX (upperChoice m (blend p q t)) (e.symm w) y =
    interpolate (jointX (upperChoice m p) (e.symm w) y) (jointX (upperChoice m q) (e.symm w) y) t.val
  rcases e.symm w with w | (w | w)
  · exact lowerAttached_blend m p q t w.val (slabHeight 0 y)
  · by_cases h : y ≤ 1 / 2
    · simp only [jointX, jointWire, Wire.atBounds, Wire.splice, spliceX, ite_eq_left h]
      exact lowerAttached_blend m p q t w.val (slabHeight 0 y)
    · simp only [jointX, jointWire, Wire.atBounds, Wire.splice, spliceX, ite_eq_right h]
      exact (interpolate_id _ _).symm
  · exact (interpolate_id _ _).symm

noncomputable def choiceLowerId (w : Fin A) : Fin (choiceWireCount m) :=
  lowerId (lower := lowerAttached m (straightChoice m)) (upper := upper)
    (lowerId (lower := lower) (upper := polygonalDrawing (straightChoice m)) w)

noncomputable def choiceUpperId (w : Fin B) : Fin (choiceWireCount m) :=
  (upperChoice m (straightChoice m)).upperId w

noncomputable def choiceCollarId (w : Fin (collarCount lower)) : Fin (choiceWireCount m) :=
  lowerId (lower := lowerAttached m (straightChoice m)) (upper := upper)
    ((lowerChoice m (straightChoice m)).upperId w)

theorem glueChoice_lower (w : Fin A) {y : ℝ} (hy : y ≤ 1 / 4) :
    (glueChoice m p).x (choiceLowerId m w) y = lower.x w (slabHeight 0 (slabHeight 0 y)) := by
  change (assemble (upperChoice m p)).x (lowerId (lower := lowerAttached m p) (upper := upper)
    (lowerId (lower := lower) (upper := polygonalDrawing p) w)) y = _
  rw [assemble_x_lower _ _ (by linarith)]
  exact assemble_x_lower (lowerChoice m p) w (by unfold slabHeight; linarith)

theorem glueChoice_upper (w : Fin B) {y : ℝ} (hy : 1 / 2 ≤ y) :
    (glueChoice m p).x (choiceUpperId m w) y = upper.x w (slabHeight 1 y) := by
  exact assemble_x_upper (upperChoice m p) w hy

theorem glueChoice_collar (w : Fin (collarCount lower)) {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (glueChoice m p).x (choiceCollarId m w) y = (p.wire w).x (4 * y - 1) := by
  change (assemble (upperChoice m p)).x (lowerId (lower := lowerAttached m p) (upper := upper) ((lowerChoice m p).upperId w)) y = _
  rw [assemble_x_lower _ _ hy.2]
  change (assemble (lowerChoice m p)).x ((lowerChoice m p).upperId w) (slabHeight 0 y) = _
  rw [assemble_x_upper _ _ (by unfold slabHeight; linarith [hy.1])]
  change (p.wire w).x (slabHeight 1 (slabHeight 0 y)) = _
  congr 1
  unfold slabHeight
  ring

private theorem lowerAttached_fixed_low (w : Fin (wireCount lower (polygonalDrawing (S := S) p)))
    {y : ℝ} (hy : y ≤ 1 / 2) :
    (lowerAttached m p).x w y = (lowerAttached m q).x w y := by
  let e := numbering lower (polygonalDrawing (S := S) p)
  change jointX (lowerChoice m p) (e.symm w) y = jointX (lowerChoice m q) (e.symm w) y
  rcases e.symm w with w | (w | w)
  · rfl
  · simp only [jointX, jointWire, Wire.atBounds, Wire.splice, spliceX, ite_eq_left hy]
  · exact (w.property rfl).elim

theorem glueChoice_fixed_outside (w : Fin (choiceWireCount m)) {y : ℝ}
    (covered : (glueChoice m p).covers w y) (outside : y ≤ 1 / 4 ∨ 1 / 2 ≤ y) :
    (glueChoice m p).x w y = (glueChoice m q).x w y := by
  let e := numbering (lowerAttached m p) upper
  have ends : y ≤ wireHi (upperChoice m p) (e.symm w) := covered.2
  change jointX (upperChoice m p) (e.symm w) y = jointX (upperChoice m q) (e.symm w) y
  rcases he : e.symm w with w | (w | w)
  · rcases outside with low | high
    · exact lowerAttached_fixed_low m p q w.val (by unfold slabHeight; linarith)
    · exact ((hi_left_lt (upperChoice m p) w).not_ge (high.trans (he ▸ ends))).elim
  · rcases outside with low | high
    · have h : y ≤ 1 / 2 := by linarith
      simp only [jointX, jointWire, Wire.atBounds, Wire.splice, spliceX, ite_eq_left h]
      exact lowerAttached_fixed_low m p q w.val (by unfold slabHeight; linarith)
    · have fixed (c : PolygonalCollar m.collarSpec) :
          jointX (upperChoice m c) (.inr (.inl w)) y =
            upper.x ((upperChoice m p).contact w).val (slabHeight 1 y) :=
        (lowerSegment (lower := lowerAttached m c) w).splice_x_upper (upperSegment (upperChoice m c) w)
          (segment_contact (upperChoice m c) w) high
      exact (fixed p).trans (fixed q).symm
  · rfl

theorem glueChoice_continuous (w : Fin (choiceWireCount m)) :
    Continuous (fun z : PolygonalCollar.Time × {y : ℝ // (glueChoice m p).covers w y} =>
      ((glueChoice m (blend p q z.1)).wire w).point z.2.val) := by
  have hl := ((glueChoice m p).wire w).continuous.domRestrict
  have hr : Continuous (fun y : {y : ℝ // (glueChoice m p).covers w y} => (glueChoice m q).x w y.val) :=
    ((glueChoice m q).wire w).continuous.domRestrict
  have he : (fun z : PolygonalCollar.Time × {y : ℝ // (glueChoice m p).covers w y} =>
      ((glueChoice m (blend p q z.1)).wire w).point z.2.val) =
    (fun z => (interpolate ((glueChoice m p).x w z.2.val) ((glueChoice m q).x w z.2.val) z.1.val, z.2.val)) := by
    funext z
    exact Prod.ext (glueChoice_blend m p q z.1 w z.2.val) rfl
  rw [he]
  exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (hl.comp continuous_snd)).add ((continuous_subtype_val.comp continuous_fst).mul
      (hr.comp continuous_snd))).prodMk (continuous_subtype_val.comp continuous_snd)

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
