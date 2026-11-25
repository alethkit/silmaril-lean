module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarAmbient
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarCombined.Paste
import Mathlib.Tactic.NormNum

public section

/-!
# Combining fixed-contact isotopies at both joins

This is the fixed-contact ambient compatibility for the sequential
juxtaposition in Figure 7 and Lemma 3.4 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5, p. 9:7.
The pinned PDF SHA-256 is
`8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch

open SlabIsotopy (Time place)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)
variable (p q : PolygonalCollar m.collarSpec) (l : lower.AmbientMotion) (r : upper.AmbientMotion)

/-- Paste the operand motions through the actual two joins, holding the
chosen collar fixed. -/
noncomputable def glueWithOperandMotions : (m.glueWith p).AmbientMotion :=
  Proofs.CollarCombined.fixed m p l r

/-- At each single time, glue the actual lower operand, blended collar, and
upper operand frames using the transported typed cap matches. -/
noncomputable def glueWithMotions : (m.glueWith p).AmbientMotion :=
  Proofs.CollarCombined.moving m p q l r

theorem glueWithMotions_lower (t : Time) (z : ℝ × ℝ) (h : z.2 ≤ 1 / 4) :
    (m.glueWithMotions p q l r).isotopy.frame t z =
      place 0 (place 0 (l.isotopy.frame t ((place 0).symm ((place 0).symm z)))) :=
  Proofs.CollarCombined.moving_lower m p q l r t z h

theorem glueWithMotions_upper (t : Time) (z : ℝ × ℝ) (h : 1 / 2 ≤ z.2) :
    (m.glueWithMotions p q l r).isotopy.frame t z = r.isotopy.placed 1 t z :=
  Proofs.CollarCombined.moving_upper m p q l r t z h

theorem glueWithMotions_middle (t : Time) (z : ℝ × ℝ)
    (h : z.2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (m.glueWithMotions p q l r).isotopy.frame t z = p.ambientIsotopy q t z :=
  Proofs.CollarCombined.moving_middle m p q l r t z h

/-- The disjoint-support composition, with both factors taken at the same time. -/
theorem glueWithMotions_apply (t : Time) (z : ℝ × ℝ) :
    (m.glueWithMotions p q l r).isotopy.frame t z =
      p.ambientIsotopy q t ((m.glueWithOperandMotions p l r).isotopy.frame t z) :=
  Proofs.CollarCombined.frame_comp m p q l r t z

theorem glueWithMotions_lower_splice (t : Time) (x : ℝ) :
    (m.glueWithMotions p q l r).isotopy.frame t (x, 1 / 4) = (x, 1 / 4) := by
  rw [m.glueWithMotions_middle p q l r t _ (by norm_num [Set.mem_Icc])]
  exact p.ambientIsotopy_outside q t _ (.inl le_rfl)

theorem glueWithMotions_upper_splice (t : Time) (x : ℝ) :
    (m.glueWithMotions p q l r).isotopy.frame t (x, 1 / 2) = (x, 1 / 2) := by
  rw [m.glueWithMotions_middle p q l r t _ (by norm_num [Set.mem_Icc])]
  exact p.ambientIsotopy_outside q t _ (.inr le_rfl)

theorem glueWithMotions_continuous :
    Continuous (fun z : Time × (ℝ × ℝ) => (m.glueWithMotions p q l r).isotopy.frame z.1 z.2) :=
  (m.glueWithMotions p q l r).isotopy.continuous_frame

theorem glueWithMotions_inverse_continuous :
    Continuous (fun z : Time × (ℝ × ℝ) => ((m.glueWithMotions p q l r).isotopy.frame z.1).symm z.2) :=
  (m.glueWithMotions p q l r).isotopy.continuous_inverse

/-- Each full trace follows the same wire equivalence that transports
labels, incidence and the ordered ports in the re-glued drawing. -/
theorem glueWithMotions_trace (t : Time) (w : Fin m.gluedWireCount) :
    (m.glueWithMotions p q l r).isotopy.frame t '' ((m.glueWith p).wire w).trace =
      (((m.glueWithMotions p q l r).drawing t).wire
        (((m.glueWithMotions p q l r).correspondence t).rename w)).trace :=
  ((m.glueWithMotions p q l r).correspondence t).trace w

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch
