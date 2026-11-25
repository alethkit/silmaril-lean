module

public import Silmaril.Courses.Cambridge.Subtyping.L3Examples

/-! # Why mutable references are invariant (Exercise 33)

Each alternative adds one of slide 214's rules to the typing judgments for the
examples. Both witnesses take steps in the shared L3 semantics.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping.Examples

open L3 (Ty Expr Value Store Step Steps Stuck)

def CovariantRefs (source target : Ty) : Prop :=
  L3Subty source target ∨ ∃ A B, source = .ref A ∧ target = .ref B ∧ L3Subty A B

def ContravariantRefs (source target : Ty) : Prop :=
  L3Subty source target ∨ ∃ A B, source = .ref A ∧ target = .ref B ∧ L3Subty B A

/-- Write a narrow record through a widened reference and read it at its original type. -/
def covarianceProgram : Expr :=
  .letE (.ref typePQ) (.ref valuePQ.val)
    (.letE (.ref typeP) (.bvar 0)
      (.seq (.assign (.bvar 0) valueP.val) (.project (.deref (.bvar 1)) "q")))

/-- Read a narrow record through a reference that claims it has another field. -/
def contravarianceProgram : Expr :=
  .letE (.ref typeP) (.ref valueP.val)
    (.letE (.ref typePQ) (.bvar 0) (.project (.deref (.bvar 0)) "q"))

theorem covarianceProgram_typed : Typing CovariantRefs ∅ .empty covarianceProgram .int :=
  .letE (.ref (.record (fun _ => .int _)))
    (.letE (.sub (.bvar rfl) (.inr ⟨_, _, rfl, rfl, typePQ_sub_typeP⟩))
      (.seq (.assign (.bvar rfl) (.record (fun _ => .int _)))
        (.project (labels := labelsPQ) (types := fun _ => .int) 1 (.deref (.bvar rfl)))))

theorem contravarianceProgram_typed :
    Typing ContravariantRefs ∅ .empty contravarianceProgram .int :=
  .letE (.ref (.record (fun _ => .int _)))
    (.letE (.sub (.bvar rfl) (.inr ⟨_, _, rfl, rfl, typePQ_sub_typeP⟩))
      (.project (labels := labelsPQ) (types := fun _ => .int) 1 (.deref (.bvar rfl))))

def badStore : Store := (∅ : Store).insert 0 valueP

theorem missingField_stuck : Stuck ⟨.project valueP.val "q", badStore⟩ := by
  constructor
  · intro value
    cases value
  · intro next step
    change Step ⟨.project (.record labelsP (fun _ => .int 3)) "q", badStore⟩ next at step
    generalize name : ("q" : String) = label at step
    cases step with
    | projectStep step =>
      cases step with
      | recordStep i _ inner =>
        change Step ⟨.int 3, _⟩ _ at inner
        cases inner
    | projectValue i _ =>
      have first : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact (by decide : ("q" : String) ≠ "p") name

theorem covarianceProgram_trace :
    Steps ⟨covarianceProgram, ∅⟩ ⟨.project valueP.val "q", badStore⟩ := by
  have allocate : Step ⟨.ref valuePQ.val, ∅⟩
      ⟨.loc 0, (∅ : Store).insert 0 valuePQ⟩ :=
    .refValue valuePQ Finmap.notMem_empty
  have write : Step ⟨.assign (.loc 0) valueP.val, (∅ : Store).insert 0 valuePQ⟩
      ⟨.skip, badStore⟩ := by
    simpa only [badStore, Finmap.insert_insert] using
      Step.assignValue valueP (s := (∅ : Store).insert 0 valuePQ) (loc := 0) (by simp)
  refine .head (.letStep allocate) (.head (.letValue (.loc 0)) (.head (.letValue (.loc 0)) ?_))
  refine .head (.seqStep write) (.head .seqSkip ?_)
  exact .single (.projectStep (.derefValue (by simp [badStore])))

theorem contravarianceProgram_trace :
    Steps ⟨contravarianceProgram, ∅⟩ ⟨.project valueP.val "q", badStore⟩ := by
  have allocate : Step ⟨.ref valueP.val, ∅⟩ ⟨.loc 0, badStore⟩ :=
    .refValue valueP Finmap.notMem_empty
  refine .head (.letStep allocate) (.head (.letValue (.loc 0)) (.head (.letValue (.loc 0)) ?_))
  exact .single (.projectStep (.derefValue (by simp [badStore])))

end Silmaril.Courses.Cambridge.Subtyping.Examples
