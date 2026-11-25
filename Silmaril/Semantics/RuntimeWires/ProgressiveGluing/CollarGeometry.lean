module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarDefs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarGeometry
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.CollarSpec

universe u v

variable {O : Type u} {W : ℕ} (c : CollarSpec O W)

noncomputable def drawing (S : Signature.{u,v} O) : Diagram S 0 W .point :=
  Proofs.ProgressiveGluing.collarDrawing c

variable {S : Signature.{u,v} O}

theorem drawing_label (w : Fin W) : (c.drawing S).label w = c.label w := by rfl
theorem drawing_start (w : Fin W) : (c.drawing S).start w = none := by rfl
theorem drawing_finish (w : Fin W) : (c.drawing S).finish w = none := by rfl

theorem drawing_x (w : Fin W) (y : ℝ) :
    (c.drawing S).x w y = interpolate (c.bottom w) (c.top w) y := by rfl

theorem drawing_bottom (w : Fin W) : (c.drawing S).x w 0 = c.bottom w := by
  rw [c.drawing_x]
  norm_num [interpolate]

theorem drawing_top (w : Fin W) : (c.drawing S).x w 1 = c.top w := by
  rw [c.drawing_x]
  norm_num [interpolate]

/-- Every closed cut of the collar preserves the strict cap order. -/
theorem drawing_order (a b : Fin W) {y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    (c.drawing S).x a y < (c.drawing S).x b y ↔ c.bottom a < c.bottom b :=
  Proofs.ProgressiveGluing.collar_order c hy

theorem drawing_crosses (w : Fin W) {y : ℝ} (hy : y ∈ Set.Ioo 0 1) :
    (c.drawing S).crosses w y := hy

end Silmaril.RuntimeWires.ProgressiveGraph.CollarSpec
