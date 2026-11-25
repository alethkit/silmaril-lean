module

public import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.PolygonalSwap.Transport
import Silmaril.Semantics.RuntimeWires.Polygonal.Thms
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor : ℝ} {e f : S.Edge}

namespace Box

theorem incoming_disjoint (b : Box S floor e) (h : BoxAltitude)
    {i j : Fin (S.source e).length} (hij : i ≠ j) :
    Disjoint (b.incoming h i).trace (b.incoming h j).trace :=
  connector_trace_disjoint _ _ _ hij

theorem outgoing_disjoint (b : Box S floor e) (h : BoxAltitude)
    {i j : Fin (S.target e).length} (hij : i ≠ j) :
    Disjoint (b.outgoing h i).trace (b.outgoing h j).trace :=
  connector_trace_disjoint _ _ _ hij

theorem input_output_disjoint (b : Box S floor e) (h : BoxAltitude)
    (i : Fin (S.source e).length) (j : Fin (S.target e).length) :
    Disjoint (b.incoming h i).trace (b.outgoing h j).trace :=
  Proofs.PolygonalSwap.input_output_disjoint b h i j

/-- Each incoming strand meets its box at its designated input port. -/
theorem incoming_contact (b : Box S floor e) (h : BoxAltitude) (i : Fin (S.source e).length) :
    (b.incoming h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.input.coordinate i, h.val)} :=
  Proofs.PolygonalSwap.incoming_contact b h i

/-- Each outgoing strand meets its box at its designated output port. -/
theorem outgoing_contact (b : Box S floor e) (h : BoxAltitude) (i : Fin (S.target e).length) :
    (b.outgoing h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.output.coordinate i, h.val + 1)} :=
  Proofs.PolygonalSwap.outgoing_contact b h i

end Box

namespace BoxPair

variable (d : BoxPair S floor e f)

theorem columns_disjoint (h k : BoxAltitude) :
    Disjoint (d.first.column h) (d.second.column k) :=
  Proofs.PolygonalSwap.columns_disjoint d h k

theorem middle_altitudes : firstAltitude swapMiddle = secondAltitude swapMiddle := by
  apply Subtype.ext
  norm_num [firstAltitude, secondAltitude, swapMiddle]

theorem snapshot_inside (t : SwapTime) : d.snapshot t ⊆ d.rectangle :=
  Proofs.PolygonalSwap.snapshot_inside d t

/-- An ambient homeomorphism of the closed enclosing rectangle at each time. -/
noncomputable def deformation (t : SwapTime) : d.rectangle ≃ₜ d.rectangle :=
  Proofs.PolygonalSwap.deformation d t

theorem continuous_deformation :
    Continuous (fun q : SwapTime × d.rectangle => d.deformation q.1 q.2) :=
  Proofs.PolygonalSwap.continuous_deformation d

theorem continuous_deformation_inverse :
    Continuous (fun q : SwapTime × d.rectangle => (d.deformation q.1).symm q.2) :=
  Proofs.PolygonalSwap.continuous_deformation_inverse d

theorem deformation_start (p : d.rectangle) : d.deformation swapStart p = p :=
  Proofs.PolygonalSwap.deformation_start d p

/-- All four sides are fixed pointwise throughout the deformation. -/
theorem deformation_fixed (t : SwapTime) (p : d.rectangle) (hp : d.OnBoundary p.val) :
    d.deformation t p = p :=
  Proofs.PolygonalSwap.deformation_fixed d t p hp

theorem deformation_horizontal (t : SwapTime) (p : d.rectangle) :
    (d.deformation t p).val.1 = p.val.1 :=
  Proofs.PolygonalSwap.deformation_horizontal d t p

/-- A vertical through-wire spanning the rectangle retains its full trace. -/
theorem deformation_fiber (t : SwapTime) (x : ℝ) :
    d.deformation t '' {p : d.rectangle | p.val.1 = x} = {p : d.rectangle | p.val.1 = x} :=
  Proofs.PolygonalSwap.deformation_fiber d t x

/-- Every vertical fiber keeps its strict height order. -/
theorem deformation_vertical (t : SwapTime) {p q : d.rectangle}
    (hx : p.val.1 = q.val.1) (hy : p.val.2 < q.val.2) :
    (d.deformation t p).val.2 < (d.deformation t q).val.2 :=
  Proofs.PolygonalSwap.deformation_vertical d t hx hy

/-- The homeomorphism sends each indexed cell of the first box to its exact trace at time `t`. -/
theorem first_cell_image (t : SwapTime) (c : BoxCell S e) :
    d.deformation t '' (Subtype.val ⁻¹' d.first.cell (firstAltitude swapStart) c) =
      Subtype.val ⁻¹' d.first.cell (firstAltitude t) c :=
  Proofs.PolygonalSwap.first_cell d t c

/-- The homeomorphism sends each indexed cell of the second box to its exact trace at time `t`. -/
theorem second_cell_image (t : SwapTime) (c : BoxCell S f) :
    d.deformation t '' (Subtype.val ⁻¹' d.second.cell (secondAltitude swapStart) c) =
      Subtype.val ⁻¹' d.second.cell (secondAltitude t) c :=
  Proofs.PolygonalSwap.second_cell d t c

/-- Compare points in the first slot at the same reference height. -/
theorem deformation_first_height (t : SwapTime) (p : d.rectangle)
    (hx : p.val.1 ∈ Set.Icc d.first.left d.first.right) {y : ℝ}
    (hy : p.val.2 = rescale (firstAltitude swapStart) y) :
    (d.deformation t p).val.2 = rescale (firstAltitude t) y :=
  Proofs.PolygonalSwap.first_height d t p hx hy

/-- Compare points in the second slot at the same reference height. -/
theorem deformation_second_height (t : SwapTime) (p : d.rectangle)
    (hx : p.val.1 ∈ Set.Icc d.second.left d.second.right) {y : ℝ}
    (hy : p.val.2 = rescale (secondAltitude swapStart) y) :
    (d.deformation t p).val.2 = rescale (secondAltitude t) y :=
  Proofs.PolygonalSwap.second_height d t p hx hy

theorem snapshot_image (t : SwapTime) :
    d.deformation t '' (Subtype.val ⁻¹' d.snapshot swapStart) = Subtype.val ⁻¹' d.snapshot t :=
  Proofs.PolygonalSwap.snapshot_image d t

theorem first_cut :
    d.snapshot swapStart ∩ {p | p.2 = 3} = {p | p.1 ∈ d.firstSeam.positions ∧ p.2 = 3} :=
  Proofs.PolygonalSwap.first_cut d

theorem second_cut :
    d.snapshot swapFinish ∩ {p | p.2 = 3} = {p | p.1 ∈ d.secondSeam.positions ∧ p.2 = 3} :=
  Proofs.PolygonalSwap.second_cut d

open Silmaril.RuntimeWires.Sliced

/-- The two geometric endpoint schedules arise by splitting the same parallel row. -/
theorem schedule_swap (e f : S.Edge) :
    Sheet.SeamEquivalent (firstThenSecond S e f) (secondThenFirst S e f) :=
  Proofs.PolygonalSwap.schedule_swap e f

end BoxPair
end Silmaril.RuntimeWires.Polygonal
