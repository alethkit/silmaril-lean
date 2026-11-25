module

public import Silmaril.Courses.Cambridge.L2.DenotationalInstitution
public import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Examples
import Silmaril.Courses.Cambridge.L2.Denotation.Operational
import Mathlib.Data.Fin.VecNotation

/-! # Recursive and looping returns in the L2 catalogue -/

public section

namespace Silmaril.Courses.Cambridge.L2.DenotationalInstitution.Examples

open RelationalDenotation.Examples (cell loop loop_returns loop_small_step recursiveProgram
  recursive_returns)
open ReturnSpecification (Holds Sentence)
open StepSpecification (Catalogue Context)

/-- The recursive result is outside the catalogue. The loop's two proposed
targets have the same expression and differ by the last guard's write. -/
abbrev context : Context := ⟨.l2, 4⟩

def catalogue : Catalogue context :=
  ![⟨recursiveProgram, cell 3⟩, ⟨loop, cell 0⟩, ⟨.skip, cell 3⟩, ⟨.skip, cell 2⟩]

def sentence : Sentence context := [.mayReturn 0, .mayReturnTo 1 2]

theorem sentence_denotes : ∀ claim ∈ sentence, Denotes (claim.map catalogue) := by
  intro claim member
  simp only [sentence, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨⟨.int 13, cell 13⟩, .int 13, recursive_returns, rfl⟩
  · exact ⟨.unit, loop_returns, rfl⟩

theorem sentence_holds : Holds context catalogue sentence :=
  (holds_iff catalogue sentence).mpr sentence_denotes

theorem stale_store_rejected : ¬ Holds context catalogue [.mayReturnTo 1 3] := by
  intro holds
  have observed : RelationalDenotation.Observes [] loop (cell 0) ⟨.skip, cell 2⟩ :=
    (holds_iff catalogue _).mp holds (.mayReturnTo 1 3) (by simp)
  obtain ⟨path, ready⟩ := (RelationalDenotation.adequate _ _ _).mp observed
  have same := RightUnique.reach_final_eq Denotation.stepRightUnique path loop_small_step
    (value_terminal ready) (value_terminal .skip)
  have reads := congrArg (fun cfg : Config => L1.Store.lookup cfg.store "l") same
  exact (by decide : L1.Store.lookup (cell 2) "l" ≠ L1.Store.lookup (cell 3) "l") reads

end Silmaril.Courses.Cambridge.L2.DenotationalInstitution.Examples
