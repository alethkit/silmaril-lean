module

import Silmaril.Courses.Cambridge.L3.OperationalInstitution

/-! Checked fresh allocation and finite may returns over the original L3 store. -/

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.Courses.Cambridge.L3
open Silmaril.Courses.Cambridge.L3.OperationalInstitution

private def cellValue : Value := ⟨.int 42, .int 42⟩
private def initialStore : Store := (∅ : Store).insert 0 ⟨.int 7, .int 7⟩
private def extendedStore (loc : Loc) : Store := initialStore.insert loc cellValue

private def allocate : Config := ⟨.ref cellValue.val, initialStore⟩
private def allocated (loc : Loc) : Config := ⟨.loc loc, extendedStore loc⟩

private theorem allocationStep {loc : Loc} (fresh : loc ∉ initialStore) :
    Step allocate (allocated loc) :=
  .refValue cellValue fresh

example (loc : Loc) (fresh : loc ∉ initialStore) :
    (Signature.institution.obj system.shape).Sat (Discrete.mk system.model)
      (allocate, (), allocated loc) :=
  (sat_iff _ _).2 (allocationStep fresh)

example (store : Store) : ¬ (Signature.institution.obj system.shape).Sat (Discrete.mk system.model)
    (allocate, (), ⟨.loc 0, store⟩) := by
  intro sat
  have step := (sat_iff _ _).1 sat
  change Step ⟨.ref (.int 42), initialStore⟩ ⟨.loc 0, store⟩ at step
  generalize Expr.int 42 = operand at step
  cases step with
  | refValue _ fresh => exact fresh (by simp [initialStore])

private def dereference : Config := ⟨.deref allocate.expr, initialStore⟩
private def result (loc : Loc) : Config := ⟨cellValue.val, extendedStore loc⟩

private theorem readRun {loc : Loc} (fresh : loc ∉ initialStore) :
    Runs system.model dereference [(), ()] (result loc) :=
  .stepL (Step.derefStep (allocationStep fresh))
    (.stepL (Step.derefValue (by simp [extendedStore])) .refl)

private theorem readMay {loc : Loc} (fresh : loc ∉ initialStore) :
    semantics.May dereference (.returned (result loc)) :=
  (may_return_iff _ _).2
    ⟨(steps_iff_reachable _ _).2 ⟨_, readRun fresh⟩, cellValue.property⟩

-- Both branches return 42. Looking up location 1 distinguishes the stores.
example : semantics.May dereference (.returned (result 1)) ∧
    semantics.May dereference (.returned (result 2)) ∧ result 1 ≠ result 2 := by
  refine ⟨readMay (by simp [initialStore, Finmap.notMem_empty]),
    readMay (by simp [initialStore, Finmap.notMem_empty]), ?_⟩
  intro equal
  have lookup := congrArg (fun c : Config => c.store.lookup 1) equal
  simp [result, extendedStore, initialStore, Finmap.lookup_insert_of_ne] at lookup
