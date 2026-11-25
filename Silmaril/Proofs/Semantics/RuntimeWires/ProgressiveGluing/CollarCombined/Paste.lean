module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarCombined.Normalize
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarMotionJoins
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarMotion
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Thms
import Mathlib.Tactic.Linarith

public section

namespace Silmaril.RuntimeWires.Proofs.CollarCombined

open ProgressiveGraph
open SlabIsotopy (Time place)
open Proofs.ProgressiveGluing (polygonalDrawing lowerChoice upperChoice)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)
variable (p q : PolygonalCollar m.collarSpec) (l : lower.AmbientMotion) (r : upper.AmbientMotion)

/-- The second match is precisely the one used by the existing chosen-collar gluing. -/
noncomputable def upperJoin : (lowerChoice m p).glue.PartialVerticalMatch upper :=
  upperChoice m p

noncomputable def moving : (m.glueWith p).AmbientMotion :=
  (upperJoin m p).glueMotion ((lowerChoice m p).glueMotion l (collarMotion p q)) r

noncomputable def fixed : (m.glueWith p).AmbientMotion :=
  (upperJoin m p).glueMotion
    ((lowerChoice m p).glueMotion l (.stationary (polygonalDrawing p))) r

theorem moving_isotopy :
    (moving m p q l r).isotopy = (l.isotopy.paste (normalized p q)).paste r.isotopy := by
  unfold moving
  rw [ProgressiveGraph.Diagram.PartialVerticalMatch.glueMotion_isotopy,
    ProgressiveGraph.Diagram.PartialVerticalMatch.glueMotion_isotopy]
  rfl

theorem fixed_isotopy :
    (fixed m p l r).isotopy =
      (l.isotopy.paste (ProgressiveGraph.Diagram.AmbientMotion.stationary
        (polygonalDrawing (S := S) p)).isotopy).paste r.isotopy := by
  unfold fixed
  rw [ProgressiveGraph.Diagram.PartialVerticalMatch.glueMotion_isotopy,
    ProgressiveGraph.Diagram.PartialVerticalMatch.glueMotion_isotopy]

theorem paste_inner_lower (f g h : SlabIsotopy) (t : Time) (z : ℝ × ℝ) (hy : z.2 ≤ 1 / 4) :
    (f.paste g |>.paste h).frame t z =
      place 0 (place 0 (f.frame t ((place 0).symm ((place 0).symm z)))) := by
  rw [SlabIsotopy.paste_lower _ _ _ _ (by linarith)]
  change place 0 ((f.paste g).frame t ((place 0).symm z)) = _
  rw [SlabIsotopy.paste_lower _ _ _ _ (by change slabHeight 0 z.2 ≤ _; unfold slabHeight; linarith)]
  rfl

theorem paste_inner_upper (f g h : SlabIsotopy) (t : Time) (z : ℝ × ℝ)
    (hy : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (f.paste g |>.paste h).frame t z = collarPlace (g.frame t (collarPlace.symm z)) := by
  rw [SlabIsotopy.paste_lower _ _ _ _ hy.2]
  change place 0 ((f.paste g).frame t ((place 0).symm z)) = _
  rw [SlabIsotopy.paste_upper _ _ _ _ (by change _ ≤ slabHeight 0 z.2; unfold slabHeight; linarith [hy.1])]
  rfl

theorem moving_lower (t : Time) (z : ℝ × ℝ) (hy : z.2 ≤ 1 / 4) :
    (moving m p q l r).isotopy.frame t z =
      place 0 (place 0 (l.isotopy.frame t ((place 0).symm ((place 0).symm z)))) := by
  rw [moving_isotopy, paste_inner_lower _ _ _ _ _ hy]

theorem moving_upper (t : Time) (z : ℝ × ℝ) (hy : 1 / 2 ≤ z.2) :
    (moving m p q l r).isotopy.frame t z = r.isotopy.placed 1 t z := by
  rw [moving_isotopy, SlabIsotopy.paste_upper _ _ _ _ hy]

theorem moving_middle (t : Time) (z : ℝ × ℝ) (hy : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (moving m p q l r).isotopy.frame t z = p.ambientIsotopy q t z := by
  rw [moving_isotopy, paste_inner_upper _ _ _ _ _ hy]
  change collarPlace (collarPlace.symm (p.ambientIsotopy q t (collarPlace (collarPlace.symm z)))) = _
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem fixed_middle (t : Time) (z : ℝ × ℝ) (hy : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (fixed m p l r).isotopy.frame t z = z := by
  rw [fixed_isotopy, paste_inner_upper _ _ _ _ _ hy]
  exact collarPlace.apply_symm_apply z

/-- The re-glued motion is exactly the composition of the operand-only
pasting and the collar isotopy at the same time. -/
theorem frame_comp (t : Time) (z : ℝ × ℝ) :
    (moving m p q l r).isotopy.frame t z =
      p.ambientIsotopy q t ((fixed m p l r).isotopy.frame t z) := by
  by_cases low : z.2 ≤ 1 / 4
  · have support : ((fixed m p l r).isotopy.frame t z).2 ≤ 1 / 4 :=
      ((fixed m p l r).isotopy.height t z).trans_le low
    rw [p.ambientIsotopy_outside q t _ (.inl support), moving_lower m p q l r t z low,
      fixed_isotopy, paste_inner_lower _ _ _ _ _ low]
  by_cases high : 1 / 2 ≤ z.2
  · have support : 1 / 2 ≤ ((fixed m p l r).isotopy.frame t z).2 :=
      high.trans_eq ((fixed m p l r).isotopy.height t z).symm
    rw [p.ambientIsotopy_outside q t _ (.inr support), moving_upper m p q l r t z high,
      fixed_isotopy, SlabIsotopy.paste_upper _ _ _ _ high]
  have mid : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) := ⟨(lt_of_not_ge low).le, (lt_of_not_ge high).le⟩
  rw [moving_middle m p q l r t z mid, fixed_middle m p l r t z mid]

end Silmaril.RuntimeWires.Proofs.CollarCombined
