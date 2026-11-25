module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Pieces
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.CapUnits

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable {a b : CapProfile O} (p : FixedDrawing S a b)

include p in
theorem bottom_inside : a.Inside := by
  intro i
  have start : p.drawing.lower (p.input i).val = 0 := by
    simp [Diagram.lower, endpointHeight, (p.input i).property]
  have bounds : p.drawing.covers (p.input i).val 0 :=
    ⟨start.le, start ▸ (p.drawing.wire (p.input i).val).increasing.le⟩
  exact p.input_x i ▸ p.drawing.wire_inside (p.input i).val 0 bounds

include p in
theorem top_inside : b.Inside := by
  intro i
  have finish : p.drawing.upper (p.output i).val = 1 := by
    simp [Diagram.upper, endpointHeight, (p.output i).property]
  have bounds : p.drawing.covers (p.output i).val 1 :=
    ⟨finish ▸ (p.drawing.wire (p.output i).val).increasing.le, finish.ge⟩
  exact p.output_x i ▸ p.drawing.wire_inside (p.output i).val 1 bounds

theorem identity_x (h : a.Inside) (i : Fin a.size) (y : ℝ) :
    (FixedDrawing.identity S a h).drawing.x i y = a.x i := by
  change ((FixedDrawing.identitySpec a h).drawing S).x i y = a.x i
  rw [CollarSpec.drawing_x]
  change interpolate (a.x i) (a.x i) y = _
  unfold interpolate
  ring

end Silmaril.RuntimeWires.Proofs.CapUnits
