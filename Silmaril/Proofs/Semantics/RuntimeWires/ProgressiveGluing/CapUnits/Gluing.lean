module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Comparison
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Incidence
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Vertices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapUnits

open ProgressiveGraph CollarAssociator

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}
variable (p : FixedDrawing S a b)

def padding (top : Bool) (amount : ℝ) (ha : amount ∈ Set.Ioo 0 1) : Padding where
  width := Classical.choose (exists_width p.drawing top)
  amount := amount
  width_inside := (Classical.choose_spec (exists_width p.drawing top)).1
  amount_inside := ha

def leftPadding := padding p false (1 / 2) (by norm_num)
def rightPadding := padding p true (3 / 4) (by norm_num)

def leftWindow : Window p.drawing false a (leftPadding p) where
  slots := p.input
  coord := p.input_x
  beyond := (Classical.choose_spec (exists_width p.drawing false)).2

def rightWindow : Window p.drawing true b (rightPadding p) where
  slots := p.output
  coord i := by simpa [radius] using p.output_x i
  beyond := (Classical.choose_spec (exists_width p.drawing true)).2

theorem left_height (y : ℝ) :
    radius false ((leftPadding p).placed y) = Height.upper (radius false y) := by
  simp only [radius, Bool.false_eq_true, ite_false, leftPadding, padding, Padding.placed, Height.upper, halfHeight]
  ring

theorem right_height (y : ℝ) :
    radius true ((rightPadding p).placed y) = Height.lower (radius true y) := by
  simp only [radius, ite_true, rightPadding, padding, Padding.placed, Height.lower, halfHeight]
  ring

theorem same_contact_line (x t : ℝ) : interpolate x x t = x := by
  unfold interpolate
  ring

theorem left_pad (h : a.Inside) (i : Fin a.size) (y : ℝ) (hy : y ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    (a.x i, y) ∈ ((leftMatch p h).glue.wire (rightWire (leftMatch p h) (p.input i).val)).trace := by
  let m := leftMatch p h
  apply (trace_mem m.glue _ _).mpr
  apply (collared_expand m id id _ _).mpr
  rcases le_total y (1 / 4 : ℝ) with low | high
  · refine .inl ⟨i, 4 * y, left_name p h i, ?_, ?_⟩
    · exact (vertex_free_covers _).mpr ⟨by linarith [hy.1], by linarith⟩
    · change ((FixedDrawing.identity S a h).drawing.x i (4 * y), Height.lower (4 * y)) = _
      rw [identity_x]
      congr 1
      unfold Height.lower halfHeight
      ring
  · let c := (FixedDrawing.identity S a h).output i
    refine .inr (.inl ⟨c, 4 * y - 1, left_name p h i, ⟨by linarith, by linarith [hy.2]⟩, ?_⟩)
    change (interpolate ((FixedDrawing.identity S a h).drawing.x c.val 1)
        (p.drawing.x (m.contact c).val 0) (4 * y - 1), Height.collar (4 * y - 1)) = _
    change (interpolate ((FixedDrawing.identity S a h).drawing.x i 1)
        (p.drawing.x (m.contact ((FixedDrawing.identity S a h).output i)).val 0) (4 * y - 1),
      Height.collar (4 * y - 1)) = _
    rw [identity_x, left_contact, p.input_x, same_contact_line]
    congr 1
    unfold Height.collar halfHeight
    ring

theorem right_pad (h : b.Inside) (i : Fin b.size) (y : ℝ) (hy : y ∈ Set.Icc 0 (3 / 4 : ℝ)) :
    (b.x i, 1 - y) ∈ ((rightMatch p h).glue.wire (leftWire (rightMatch p h) (p.output i).val)).trace := by
  let m := rightMatch p h
  apply (trace_mem m.glue _ _).mpr
  apply (collared_expand m id id _ _).mpr
  rcases le_total (1 - y) (1 / 2 : ℝ) with low | high
  · refine .inr (.inl ⟨p.output i, 4 * (1 - y) - 1, rfl, ⟨by linarith [hy.2], by linarith⟩, ?_⟩)
    change (interpolate (p.drawing.x (p.output i).val 1)
      ((FixedDrawing.identity S b h).drawing.x (m.contact (p.output i)).val 0) (4 * (1 - y) - 1),
      Height.collar (4 * (1 - y) - 1)) = _
    rw [p.output_x, right_contact]
    change (interpolate (b.x i) ((FixedDrawing.identity S b h).drawing.x i 0) (4 * (1 - y) - 1),
      Height.collar (4 * (1 - y) - 1)) = _
    rw [identity_x, same_contact_line]
    congr 1
    unfold Height.collar halfHeight
    ring
  · refine .inr (.inr ⟨i, 2 * (1 - y) - 1, right_name p h i, ?_, ?_⟩)
    · exact (vertex_free_covers _).mpr ⟨by linarith, by linarith [hy.1]⟩
    · change ((FixedDrawing.identity S b h).drawing.x i (2 * (1 - y) - 1),
        Height.upper (2 * (1 - y) - 1)) = _
      rw [identity_x]
      congr 1
      unfold Height.upper halfHeight
      ring

def leftPlaced (h : a.Inside) : (leftWindow p).Placed (leftMatch p h).glue where
  incidence := leftIncidence p h
  vertexX j :=
    (congrArg (leftMatch p h).glue.vertexX (leftIncidence_vertex p h j)).trans (vertexX_upper _ j)
  height j := by
    rw [left_height, radius_involutive]
    exact (congrArg (leftMatch p h).glue.vertexHeight (leftIncidence_vertex p h j)).trans (height_upper _ j)
  core w y hw := by
    rw [left_height]
    apply (trace_mem (leftMatch p h).glue _ _).mpr
    apply (collared_expand (leftMatch p h) id id _ _).mpr
    exact .inr (.inr ⟨w, radius false y, rfl, hw, rfl⟩)
  pad i y hy := left_pad p h i y hy

def rightPlaced (h : b.Inside) : (rightWindow p).Placed (rightMatch p h).glue where
  incidence := rightIncidence p h
  vertexX := vertexX_lower _
  height j := by
    rw [right_height, radius_involutive]
    exact height_lower _ j
  core w y hw := by
    rw [right_height]
    apply (trace_mem (rightMatch p h).glue _ _).mpr
    apply (collared_expand (rightMatch p h) id id _ _).mpr
    exact .inl ⟨w, radius true y, rfl, hw, rfl⟩
  pad i y hy := right_pad p h i y hy

end Silmaril.RuntimeWires.Proofs.CapUnits
