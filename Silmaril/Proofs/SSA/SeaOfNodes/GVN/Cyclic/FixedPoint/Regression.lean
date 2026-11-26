module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Regression

open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint
open Silmaril.SSA.SeaOfNodes.Diamond (Signature ValueSort)

private abbrev int : ValueSort Unit := .data ()

private abbrev NoPrimitives : Signature Unit := fun _ _ => Empty

local instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

private abbrev sorts : Fin 4 → ValueSort Unit := fun _ => int
private abbrev inputs := [int, int]

/-- Two feedback cycles, 0 ↔ 2 and 1 ↔ 3. Only vertex 3 reads the second
entry argument, giving it a different entry occurrence from the other Phis. -/
private def node (i : Fin 4) : Node NoPrimitives inputs sorts (sorts i) :=
  match i.val with
  | 0 => .phi .head (.producer 2 rfl)
  | 1 => .phi .head (.producer 3 rfl)
  | 2 => .phi .head (.producer 0 rfl)
  | _ => .phi (.tail .head) (.producer 1 rfl)

private def fixture : Graph NoPrimitives inputs sorts where
  node := node
  ordered i _ _ pureNode _ := by
    unfold node at pureNode
    split at pureNode <;> cases pureNode

private def oneRound := run fixture 1 (seed fixture)
private def twoRounds := run fixture 2 (seed fixture)
private def result := normalize fixture

theorem second_round_is_needed :
    checkStable fixture oneRound = false ∧ oneRound 0 = oneRound 1 ∧
      checkStable fixture twoRounds = true ∧ twoRounds 0 ≠ twoRounds 1 := by
  decide

theorem class_count_grows_at_each_split :
    classCount (seed fixture) = 1 ∧ classCount oneRound = 2 ∧ classCount twoRounds = 3 := by
  decide

theorem normalize_retains_only_congruent_cycle :
    result 0 = result 2 ∧ result 0 ≠ result 1 ∧ result 1 ≠ result 3 ∧ result 0 ≠ result 3 := by
  decide

private def renumbered (i : Fin 4) : Fin 4 := (result i).rev

theorem accepts_stable_noncanonical_labels :
    checkStable fixture renumbered = true ∧
      run fixture 1 renumbered = renumbered ∧ refine fixture renumbered 0 ≠ renumbered 0 := by
  have accepted : checkStable fixture renumbered = true := by decide
  exact ⟨accepted, by simp only [run, accepted, ite_true], by decide⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Regression
