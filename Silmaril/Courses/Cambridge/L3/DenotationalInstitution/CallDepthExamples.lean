module

import Silmaril.Courses.Cambridge.L3.DenotationalInstitution
import Silmaril.Courses.Cambridge.L3.Denotation.CallDepth.LetBoundExample
import Mathlib.Data.Fin.VecNotation

/-! The let-bound call satisfies two named fresh returns and rejects a stale store. -/

namespace Silmaril.Courses.Cambridge.L3.DenotationalInstitution.CallDepth.Examples

open Denotation (integer)
open Denotation.CallDepth.LetBoundExample (program program_admitted program_returns_iff)
open ReturnSpecification (Holds Sentence)

private def source : Config := ⟨program, ∅⟩

private def resultAt (a : Loc) : Config := ⟨.int 5, (∅ : Store).insert a (integer 5)⟩

private def oldStore : Config := ⟨.int 5, (∅ : Store).insert 0 (integer 4)⟩

private abbrev context : StepSpecification.Context := ⟨.l3, 4⟩

private def catalogue : StepSpecification.Catalogue context :=
  ![source, resultAt 0, resultAt 1, oldStore]

private def good : Sentence context := [.mayReturn 0, .mayReturnTo 0 1, .mayReturnTo 0 2]

private def stale : Sentence context := [.mayReturnTo 0 3]

private theorem observesFresh (a : Loc) : observesReturn 1 .sequenced source (resultAt a) :=
  ⟨integer 5, rfl, program_returns_iff.mpr ⟨a, Finmap.notMem_empty, rfl, rfl⟩⟩

private theorem oldStore_not_observed : ¬ observesReturn 1 .sequenced source oldStore := by
  rintro ⟨v, _, returned⟩
  obtain ⟨a, _, _, storeEq⟩ := program_returns_iff.mp returned
  have lookup := congrArg (fun store : Store => store.lookup 0) storeEq
  by_cases same : 0 = a
  · subst a
    simp [oldStore, integer] at lookup
  · simp [oldStore, source, Finmap.lookup_insert_of_ne, same] at lookup

example : Holds context catalogue good := by
  apply (holds_iff 1 .sequenced catalogue good ?_).mpr
  · intro claim member
    simp only [good, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨resultAt 0, observesFresh 0⟩
    · exact observesFresh 0
    · exact observesFresh 1
  · intro claim member
    simp only [good, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact program_admitted ∅

example : ¬ Holds context catalogue stale := by
  intro holds
  have admitted : ∀ claim ∈ stale, Admitted 1 .sequenced (claim.map catalogue) := by
    intro claim member
    obtain rfl := List.mem_singleton.mp member
    exact program_admitted ∅
  exact oldStore_not_observed
    ((holds_iff 1 .sequenced catalogue stale admitted).mp holds (.mayReturnTo 0 3) (by simp [stale]))

end Silmaril.Courses.Cambridge.L3.DenotationalInstitution.CallDepth.Examples
