module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Wire
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Assembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.VerticalMatch

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

/-- Compress the drawings into the two half-height slabs and splice every
matched pair of wires at height (1/2). Only the old vertices are present. -/
noncomputable def glue : Diagram S (L + R) W .point :=
  Proofs.ProgressiveGluing.assemble m

theorem glue_x_below (w : Fin W) {y : ℝ} (h : y ≤ 1 / 2) :
    m.glue.x w y = lower.x w (slabHeight 0 y) :=
  Proofs.ProgressiveGluing.wire_left m w h

theorem glue_x_above (w : Fin W) {y : ℝ} (h : 1 / 2 ≤ y) :
    m.glue.x w y = upper.x w (slabHeight 1 y) :=
  Proofs.ProgressiveGluing.wire_right m w h

theorem glue_x_left (j : Fin L) : m.glue.vertexX (Fin.castAdd R j) = lower.vertexX j :=
  Proofs.ProgressiveGluing.x_left j

theorem glue_x_right (j : Fin R) : m.glue.vertexX (Fin.natAdd L j) = upper.vertexX j :=
  Proofs.ProgressiveGluing.x_right j

theorem glue_height_left (j : Fin L) :
    m.glue.vertexHeight (Fin.castAdd R j) = halfHeight 0 (lower.vertexHeight j) :=
  Proofs.ProgressiveGluing.height_left j

theorem glue_height_right (j : Fin R) :
    m.glue.vertexHeight (Fin.natAdd L j) = halfHeight 1 (upper.vertexHeight j) :=
  Proofs.ProgressiveGluing.height_right j

theorem glue_generator_left (j : Fin L) :
    m.glue.generator (Fin.castAdd R j) = lower.generator j :=
  Proofs.ProgressiveGluing.generator_left j

theorem glue_generator_right (j : Fin R) :
    m.glue.generator (Fin.natAdd L j) = upper.generator j :=
  Proofs.ProgressiveGluing.generator_right j

theorem glue_label_lower : m.glue.label = lower.label := by rfl

theorem glue_label_upper : m.glue.label = upper.label := funext m.label

theorem glue_lower (w : Fin W) : m.glue.lower w = halfHeight 0 (lower.lower w) :=
  Proofs.ProgressiveGluing.low_bound w

theorem glue_upper (w : Fin W) : m.glue.upper w = halfHeight 1 (upper.upper w) :=
  Proofs.ProgressiveGluing.high_bound w

/-- The cap contact becomes an interior point of a strand. -/
theorem crosses_join (w : Fin W) : m.glue.crosses w (1 / 2) :=
  Proofs.ProgressiveGluing.join_inside m w

theorem glue_inputs_left (j : Fin L) : m.glue.inputs (Fin.castAdd R j) = lower.inputs j :=
  Proofs.ProgressiveGluing.port_list_left S.source j lower.input upper.input

theorem glue_inputs_right (j : Fin R) : m.glue.inputs (Fin.natAdd L j) = upper.inputs j :=
  Proofs.ProgressiveGluing.port_list_right S.source j lower.input upper.input

theorem glue_outputs_left (j : Fin L) : m.glue.outputs (Fin.castAdd R j) = lower.outputs j :=
  Proofs.ProgressiveGluing.port_list_left S.target j lower.output upper.output

theorem glue_outputs_right (j : Fin R) : m.glue.outputs (Fin.natAdd L j) = upper.outputs j :=
  Proofs.ProgressiveGluing.port_list_right S.target j lower.output upper.output

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.VerticalMatch
