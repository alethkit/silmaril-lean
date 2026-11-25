module

public import Silmaril.Courses.Cambridge.Subtyping.Examples
public import Silmaril.Courses.Cambridge.Subtyping.Preservation

/-! # L3 subtyping derivations and runs (slide 206 and Exercises 32–34) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping.Examples

open L3 (Ty Expr IsValue Value Store Step Steps Stuck RecordLabels)

abbrev labelsP : RecordLabels := ⟨["p"], by decide⟩
abbrev labelsPQ : RecordLabels := ⟨["p", "q"], by decide⟩
abbrev labelsQP : RecordLabels := ⟨["q", "p"], by decide⟩

def typeP : Ty := .record labelsP (fun _ => .int)
def typePQ : Ty := .record labelsPQ (fun _ => .int)
def typeQP : Ty := .record labelsQP (fun _ => .int)

theorem typePQ_sub_typeP : L3Subty typePQ typeP :=
  pq_sub_p rfl rfl

theorem typeQP_sub_typeP : L3Subty typeQP typeP :=
  reordered_argument_sub_p (pq := typePQ) (int := .int) rfl rfl rfl

def fieldsPQ (i : labelsPQ.Index) : Int := if i = 0 then 3 else 4
def fieldsQP (i : labelsQP.Index) : Int := if i = 0 then 3 else 2

def valueP : Value := ⟨.record labelsP (fun _ => .int 3), .record (fun _ => .int 3)⟩
def valuePQ : Value :=
  ⟨.record labelsPQ (fun i => .int (fieldsPQ i)), .record (fun i => .int (fieldsPQ i))⟩

/-- Slide 206. Apply the projection function to the wider record. -/
def projectionApplication : Expr :=
  .app (.lam typeP (.project (.bvar 0) "p")) valuePQ.val

theorem projectionApplication_typed : HasType ∅ .empty projectionApplication .int :=
  .app (HasType.ofL3 (.lam (.project (labels := labelsP) (types := fun _ => .int) 0 (.bvar rfl))))
    (.sub (HasType.ofL3 (.record (fun i => .int (fieldsPQ i)))) typePQ_sub_typeP)

theorem projectionApplication_trace : Steps ⟨projectionApplication, ∅⟩ ⟨.int 3, ∅⟩ :=
  .head (.appFun valuePQ.property)
    (.single (.projectValue (labels := labelsPQ) 0 (fun i => .int (fieldsPQ i))))

/-- Exercise 32(4). The first argument puts the required field second. -/
def reorderedArgumentFunction : Expr :=
  .lam (.arr typeP .int)
    (.binary (.app (.bvar 0) (.record labelsQP (fun i => .int (fieldsQP i)))) .add
      (.app (.bvar 0) (.record labelsP (fun _ => .int 4))))

theorem reorderedArgumentFunction_typed :
    HasType ∅ .empty reorderedArgumentFunction (.arr (.arr typeP .int) .int) :=
  .lam (.add (.app (.bvar rfl) (.sub (.record (fun i => .int (fieldsQP i))) typeQP_sub_typeP))
    (.app (.bvar rfl) (.record (fun _ => .int 4))))

/-- Exercise 34. A match can accept a narrower sum payload at a wider type. -/
def widenedSumMatch : Expr :=
  .matchSum (.inl valuePQ.val (.sum typePQ .unit)) typeP (.project (.bvar 0) "p") .unit (.int 0)

theorem widenedSumMatch_typed : HasType ∅ .empty widenedSumMatch .int :=
  .matchSum (.sub (.inl (.record (fun i => .int (fieldsPQ i))))
      (.sum rfl rfl typePQ_sub_typeP (.refl _)))
    (.project (labels := labelsP) (types := fun _ => .int) 0 (.bvar rfl)) (.int 0)

theorem widenedSumMatch_trace : Steps ⟨widenedSumMatch, ∅⟩ ⟨.int 3, ∅⟩ :=
  .head (.matchLeft valuePQ.property)
    (.single (.projectValue (labels := labelsPQ) 0 (fun i => .int (fieldsPQ i))))

abbrev counterLabels : RecordLabels := ⟨["get", "inc"], by decide⟩
abbrev resetCounterLabels : RecordLabels := ⟨["get", "inc", "reset"], by decide⟩

def counterMethodType {n : Nat} (i : Fin n) : Ty :=
  if i.val = 0 then .arr .unit .int else .arr .unit .unit

def counterType : Ty := .record counterLabels counterMethodType
def resetCounterType : Ty := .record resetCounterLabels counterMethodType

theorem resetCounter_sub_counter : L3Subty resetCounterType counterType :=
  reset_counter_sub_counter (unit := .unit) (int := .int) rfl rfl rfl rfl

def counterMethod (i : resetCounterLabels.Index) : Expr :=
  if i.val = 0 then .lam .unit (.deref (.bvar 1))
  else if i.val = 1 then
    .lam .unit (.assign (.bvar 1) (.binary (.int 1) .add (.deref (.bvar 1))))
  else .lam .unit (.assign (.bvar 1) (.int 0))

/-- Slides 217–218. Allocate the private cell, then use a resettable counter
through a binding that exposes just `inc` and `get`. -/
def counterProgram : Expr :=
  .letE counterType
    (.letE (.ref .int) (.ref (.int 0)) (.record resetCounterLabels counterMethod))
    (.seq (.app (.project (.bvar 0) "inc") .skip) (.app (.project (.bvar 0) "get") .skip))

theorem counterProgram_typed : HasType ∅ .empty counterProgram .int := by
  apply Typing.letE
  · refine .sub (.letE (.ref (.int 0)) (.record ?_)) resetCounter_sub_counter
    intro i
    by_cases get : i.val = 0
    · simp only [counterMethod, counterMethodType, get, ite_true]
      exact .lam (.deref (.bvar rfl))
    · by_cases inc : i.val = 1
      · simp only [counterMethod, counterMethodType, inc, ite_true]
        exact .lam (.assign (.bvar rfl) (.add (.int 1) (.deref (.bvar rfl))))
      · simp only [counterMethod, counterMethodType, get, inc, ite_false]
        exact .lam (.assign (.bvar rfl) (.int 0))
  · exact .seq
      (.app (.project (labels := counterLabels) (types := counterMethodType) 1 (.bvar rfl)) .skip)
      (.app (.project (labels := counterLabels) (types := counterMethodType) 0 (.bvar rfl)) .skip)

end Silmaril.Courses.Cambridge.Subtyping.Examples
