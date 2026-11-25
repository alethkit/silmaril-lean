module

public import Silmaril.Semantics.RuntimeWires.PolygonalCuts.Thms
import Silmaril.Semantics.RuntimeWires.Polygonal.Thms
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalCuts.Regression

open Silmaril.RuntimeWires.Polygonal Silmaril.RuntimeWires.Sliced

private inductive BoxLabel
  | create
  | scalar

private abbrev signature : Signature Bool where
  Edge := BoxLabel
  source _ := []
  target
    | .create => [true]
    | .scalar => []

private def creation : Row signature [false] [false, true] :=
  .wire false (Row.box (S := signature) BoxLabel.create .empty)

private def scalar : Row signature [false, true] [false, true] :=
  Row.box (S := signature) BoxLabel.scalar (.wire false (.wire true .empty))

private def drawing : Drawing signature 0 [false] [false, true] :=
  Drawing.realize 0 (.cons creation (.cons scalar (.empty _)))

private def departure : Frontier [false, true] := (Layer.realize 0 creation).outputs.frontier
private def arrival : Frontier [false, true] := (Layer.realize 0 scalar).inputs.frontier

private def corridor : Slab :=
  ⟨(0 : ℝ) + 1, (0 : ℝ) + 2, by norm_num⟩

private noncomputable def cut : corridor.Cut where
  height := 3 / 2
  above_lower := by norm_num [corridor]
  below_upper := by norm_num [corridor]

example : drawing.parts[1]? = some (Part.connector corridor departure arrival) := rfl

private theorem cut_positions : (cut.frontier departure arrival).positions = [2, 9 / 2] := by
  norm_num [Slab.Cut.frontier, Slab.Cut.coordinate, Slab.Cut.parameter, cut, corridor,
    connector, interpolate, departure, arrival, creation, scalar, Layer.realize, Layer.inputs,
    Layer.outputs, Through.vertical, Box.onGrid, Frontier.grid, Frontier.ofCoordinates,
    Frontier.coordinate, Frontier.singleton, Frontier.append, BoundedFrontier.prependWire,
    BoundedFrontier.prepend, BoundedFrontier.empty, Frontier.empty, List.ofFn_succ]

/-- The cut recovers the two slanted strands, with both typed ports at computed coordinates. -/
example (z : Point) :
    ((Part.connector cut.lower departure (cut.frontier departure arrival)).Contains z ∨
      (Part.connector cut.upper (cut.frontier departure arrival) arrival).Contains z) ↔
    (Part.connector corridor departure arrival).Contains z :=
  cut.connector_join departure arrival z

example (z : Point) :
    ((Part.connector cut.lower departure (cut.frontier departure arrival)).Contains z ∧
      (Part.connector cut.upper (cut.frontier departure arrival) arrival).Contains z) ↔
    z = (2, 3 / 2) ∨ z = (9 / 2, 3 / 2) := by
  rw [cut.connector_contact]
  change (∃ i : Fin 2, z = ((cut.frontier departure arrival).coordinate i, cut.height)) ↔ _
  rw [Fin.exists_fin_succ, Fin.exists_fin_one]
  simp only [Frontier.coordinate, List.get_eq_getElem, Fin.val_cast, cut_positions]
  rfl

end Silmaril.RuntimeWires.Proofs.PolygonalCuts.Regression
