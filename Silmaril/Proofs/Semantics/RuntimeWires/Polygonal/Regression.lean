module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Thms
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.Polygonal.Regression

open Silmaril.RuntimeWires.Polygonal Silmaril.RuntimeWires.Sliced

private inductive ExampleBox
  | create
  | scalar
  | remove

private abbrev exampleSignature : Signature Bool where
  Edge := ExampleBox
  source
    | .create | .scalar => []
    | .remove => [true]
  target
    | .create => [true]
    | .scalar | .remove => []

private def creation : Row exampleSignature [false] [false, true] :=
  .wire false (Row.box (S := exampleSignature) ExampleBox.create .empty)

private def scalar : Row exampleSignature [false, true] [false, true] :=
  Row.box (S := exampleSignature) ExampleBox.scalar (.wire false (.wire true .empty))

private def removal : Row exampleSignature [false, true] [false] :=
  .wire false (Row.box (S := exampleSignature) ExampleBox.remove .empty)

private def exampleSheet : Sheet exampleSignature [false] [false] :=
  .cons creation (.cons scalar (.cons removal (.empty _)))

private def exampleDrawing : Drawing exampleSignature 0 [false] [false] :=
  Drawing.realize 0 exampleSheet

example : exampleDrawing.readSheet = exampleSheet := Drawing.read_realize _ _

example : exampleDrawing.parts.length = 7 := rfl

example : ∀ piece ∈ exampleDrawing.parts, piece.Valid :=
  fun _ => Drawing.valid_parts exampleDrawing

example : exampleDrawing.parts.Pairwise (fun x y => x.slab.upper ≤ y.slab.lower) :=
  Drawing.ordered_parts exampleDrawing

private def departure : Frontier [false, true] := (Layer.realize 0 creation).outputs.frontier
private def arrival : Frontier [false, true] := (Layer.realize 0 scalar).inputs.frontier

private def corridor : Slab :=
  ⟨(0 : ℝ) + 1, (0 : ℝ) + 2, by norm_num⟩

/-- The first connector is a geometric part of the realized three-row sheet. -/
example : exampleDrawing.parts[1]? = some (Part.connector corridor departure arrival) := rfl

example : departure.positions = [1, 4] := by
  norm_num [departure, creation, Layer.realize, Layer.outputs, Through.vertical, Box.onGrid,
    Frontier.grid, Frontier.ofCoordinates, Frontier.singleton, Frontier.append,
    BoundedFrontier.prependWire, BoundedFrontier.prepend, BoundedFrontier.empty, Frontier.empty,
    List.ofFn_succ]

example : arrival.positions = [3, 5] := by
  norm_num [arrival, scalar, Layer.realize, Layer.inputs, Through.vertical, Box.onGrid,
    Frontier.grid, Frontier.ofCoordinates, Frontier.singleton, Frontier.append,
    BoundedFrontier.prependWire, BoundedFrontier.prepend, BoundedFrontier.empty, Frontier.empty,
    List.ofFn_succ]

/-- Inside the connector, each labeled strand meets the horizontal cut exactly once. -/
example : ∃ cut : Frontier ([false, true] : List Bool), ∀ i : Fin 2,
    (connector corridor departure arrival i).trace ∩ {z : Point | z.2 = (3 / 2 : ℝ)} =
      {(cut.coordinate i, 3 / 2)} :=
  connector_ordered_cut corridor departure arrival (by
    change (0 : ℝ) + 1 ≤ 3 / 2 ∧ 3 / 2 ≤ (0 : ℝ) + 2
    norm_num)

end Silmaril.RuntimeWires.Proofs.Polygonal.Regression
