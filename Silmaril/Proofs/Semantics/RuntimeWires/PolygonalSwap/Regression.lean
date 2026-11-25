module

public import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Thms
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSwap.Regression

open Silmaril.RuntimeWires.Polygonal

private inductive Generator
  | create
  | remove
  | scalar

private abbrev signature : Signature Bool where
  Edge := Generator
  source
    | .create | .scalar => []
    | .remove => [false]
  target
    | .create => [true, true]
    | .remove | .scalar => []

private noncomputable def pair (right : Generator) : BoxPair signature 0 Generator.create right :=
  let first := Box.onGrid signature 0 Generator.create
  ⟨first, Box.onGrid signature first.right right⟩

/-- A creation and a deletion pass through the same box slab without contact. -/
example :
    (BoxPair.firstAltitude swapMiddle).val = (5 / 2 : ℝ) ∧
    (BoxAltitude.body (BoxPair.firstAltitude swapMiddle)).upper = (7 / 2 : ℝ) ∧
    BoxPair.firstAltitude swapMiddle = BoxPair.secondAltitude swapMiddle ∧
    Disjoint ((pair .remove).first.column (BoxPair.firstAltitude swapMiddle))
      ((pair .remove).second.column (BoxPair.secondAltitude swapMiddle)) := by
  refine ⟨?_, ?_, BoxPair.middle_altitudes, (pair .remove).columns_disjoint _ _⟩
  · norm_num [BoxPair.firstAltitude, swapMiddle]
  · norm_num [BoxAltitude.body, Slab.unit, BoxPair.firstAltitude, swapMiddle]

private theorem first_ports : (pair .remove).firstSeam.positions = [2, 3, 6] := by
  change (Frontier.grid [true, true] ((0 : ℝ) + 2)).positions ++
    (Frontier.grid [false] ((Box.onGrid signature 0 Generator.create).right + 2)).positions = _
  norm_num [Box.onGrid, Frontier.grid, Frontier.ofCoordinates, signature, List.ofFn_succ]

private theorem second_ports : (pair .remove).secondSeam.positions = [] := rfl

/-- The seam contains three ports in one order and is empty in the other. -/
example :
    (pair .remove).snapshot swapStart ∩ {p | p.2 = 3} =
        {p | p.1 ∈ ([2, 3, 6] : List ℝ) ∧ p.2 = 3} ∧
    (pair .remove).snapshot swapFinish ∩ {p | p.2 = 3} = ∅ := by
  constructor
  · rw [(pair .remove).first_cut, first_ports]
  · rw [(pair .remove).second_cut, second_ports]
    simp

/-- The isolated scalar box moves even though its incoming and outgoing lists are empty. -/
example (t : SwapTime) :
    (pair .scalar).deformation t ''
        (Subtype.val ⁻¹' (pair .scalar).second.trace (BoxAltitude.body (BoxPair.secondAltitude swapStart))) =
      Subtype.val ⁻¹' (pair .scalar).second.trace (BoxAltitude.body (BoxPair.secondAltitude t)) :=
  (pair .scalar).second_cell_image t .body

end Silmaril.RuntimeWires.Proofs.PolygonalSwap.Regression
