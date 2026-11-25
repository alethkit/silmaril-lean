module

public import Silmaril.Semantics.RuntimeWires.PolygonalSlantedSwap.Thms
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSlantedSwap.Regression

open Silmaril.RuntimeWires.Polygonal

private abbrev signature : Signature Bool where
  Edge := Bool
  source
    | false => []
    | true => [false]
  target
    | false => [true, true]
    | true => []

private def firstBox : Box signature 0 false where
  left := 1
  right := 4
  left_bound := by norm_num
  width := by norm_num
  input := .empty
  output := Frontier.grid [true, true] 2
  input_inside := by simp [Frontier.empty]
  output_inside := by
    intro x hx
    simp [Frontier.grid, Frontier.ofCoordinates, List.ofFn_succ] at hx
    rcases hx with rfl | rfl <;> norm_num

private def secondBox : Box signature firstBox.right true where
  left := 5
  right := 7
  left_bound := by norm_num [firstBox]
  width := by norm_num
  input := Frontier.singleton false 6
  output := .empty
  input_inside := by norm_num [Frontier.singleton]
  output_inside := by simp [Frontier.empty]

private def pair : BoxPair signature 0 false true := ⟨firstBox, secondBox⟩

private noncomputable def leftPorts : ExternalPorts pair.first where
  input := .empty
  output := Frontier.grid [true, true] (3 / 2)
  input_inside := by simp [Frontier.empty]
  output_inside := by
    intro x hx
    simp [Frontier.grid, Frontier.ofCoordinates, List.ofFn_succ] at hx
    rcases hx with rfl | rfl
    · change (1 : ℝ) < 3 / 2 ∧ 3 / 2 < 4
      norm_num
    · change (1 : ℝ) < 3 / 2 + 1 ∧ 3 / 2 + 1 < 4
      norm_num

private noncomputable def rightPorts : ExternalPorts pair.second where
  input := Frontier.singleton false (13 / 2)
  output := .empty
  input_inside := by
    intro x hx
    have hx' : x = (13 / 2 : ℝ) := List.mem_singleton.mp hx
    subst x
    change (5 : ℝ) < 13 / 2 ∧ 13 / 2 < 7
    norm_num
  output_inside := by simp [Frontier.empty]

/-- The wire runs from the fixed external x-coordinate 13/2 to the box port at 6. -/
example :
    (rightPorts.incoming (BoxPair.secondAltitude swapMiddle) 0).start = (13 / 2 : ℝ) ∧
    (rightPorts.incoming (BoxPair.secondAltitude swapMiddle) 0).finish = (6 : ℝ) := by
  exact ⟨rfl, rfl⟩

example :
    (rightPorts.incoming (BoxPair.secondAltitude swapMiddle) 0).trace ∩
        pair.second.trace (BoxAltitude.body (BoxPair.secondAltitude swapMiddle)) =
      {((6 : ℝ), (5 / 2 : ℝ))} := by
  rw [rightPorts.incoming_contact]
  congr 1
  apply Prod.ext
  · rfl
  · norm_num [BoxPair.secondAltitude, swapMiddle]

/-- Transport preserves the exact slanted trace even at the equal-height frame. -/
example :
    pair.deformation swapMiddle ''
        (Subtype.val ⁻¹' (rightPorts.incoming (BoxPair.secondAltitude swapStart) 0).trace) =
      Subtype.val ⁻¹' (rightPorts.incoming (BoxPair.secondAltitude swapMiddle) 0).trace :=
  pair.slanted_second_cell_image rightPorts swapMiddle (.input 0)

example (t : SwapTime) :
    Disjoint (leftPorts.column (BoxPair.firstAltitude t)) (rightPorts.column (BoxPair.secondAltitude t)) :=
  pair.slanted_columns_disjoint leftPorts rightPorts _ _

end Silmaril.RuntimeWires.Proofs.PolygonalSlantedSwap.Regression
