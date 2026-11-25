module

public import Silmaril.Courses.Cambridge.Subtyping.Examples
public import Silmaril.Courses.Cambridge.Subtyping.Preservation

/-! # L3 subtyping derivations and runs (slide 206 and Exercises 32–34) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping.Examples

open L3 (Ty Expr IsValue Value Store Step Steps Stuck RecordLabels LocTypes VarTypes)

abbrev labelsP : RecordLabels := ⟨["p"], by decide⟩
abbrev labelsQ : RecordLabels := ⟨["q"], by decide⟩
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

/-- Exercise 32(1) on p. 87. Keep the outer field and forget the inner fields. -/
def nestedSingleton : Expr :=
  .record labelsP (fun _ => .record labelsP (fun _ => .record labelsP (fun _ =>
    .record labelsP (fun _ => .int 3))))

def singletonP (A : Ty) : Ty := .record labelsP (fun _ => A)

def emptyRecord : Ty := .record ⟨[], by decide⟩ (fun i => Fin.elim0 i)

theorem nestedSingleton_typed :
    HasType ∅ .empty nestedSingleton (singletonP emptyRecord) := by
  let inner := singletonP (singletonP typeP)
  have inferred : HasType ∅ .empty nestedSingleton (singletonP inner) :=
    .record (fun _ => .record (fun _ => .record (fun _ => .record (fun _ => .int 3))))
  have width : L3Subty inner emptyRecord :=
    .recordWidth (kept := []) (dropped := [("p", singletonP typeP)]) rfl rfl
  apply Typing.sub inferred (.recordDepth [("p", inner, emptyRecord)] rfl rfl ?_)
  intro label source target member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨rfl, rfl, rfl⟩ := member
  exact width

def intBoolRecordType : Ty := .record labelsPQ (fun i => if i = 0 then .int else .bool)

def nestedProjectionDomain : Ty :=
  .record labelsPQ (fun i => if i = 0 then .bool else intBoolRecordType)

/-- Exercise 32(2) on p. 88. Project the integer through the nested record. -/
def nestedProjectionFunction : Expr :=
  .lam nestedProjectionDomain (.project (.project (.bvar 0) "q") "p")

theorem nestedProjectionFunction_typed :
    HasType ∅ .empty nestedProjectionFunction (.arr nestedProjectionDomain .int) :=
  .lam (.project (labels := labelsPQ) (types := fun i => if i = 0 then .int else .bool) 0
    (.project (labels := labelsPQ) (types := fun i => if i = 0 then .bool else intBoolRecordType)
      1 (.bvar rfl)))

private theorem add_left_typed {Θ : LocTypes} {Γ : VarTypes} {e left right : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) (shape : e = .binary left .add right) :
    HasType Θ Γ left .int := by
  induction typed
  case add leftTyped _ _ _ => cases shape; exact leftTyped
  case sub _ _ ih => exact ih shape
  all_goals cases shape

private theorem app_typed {Θ : LocTypes} {Γ : VarTypes} {e fn arg : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) (shape : e = .app fn arg) :
    ∃ A B, HasType Θ Γ fn (.arr A B) ∧ HasType Θ Γ arg A := by
  induction typed
  case app fnTyped argTyped _ _ => cases shape; exact ⟨_, _, fnTyped, argTyped⟩
  case sub _ _ ih => exact ih shape
  all_goals cases shape

private theorem bound_subtype {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T A : Ty} {i : Nat}
    (typed : HasType Θ Γ e T) (shape : e = .bvar i) (lookup : Γ.bound[i]? = some A) :
    L3Subty A T := by
  induction typed
  case bvar found =>
    cases shape
    cases Option.some.inj (lookup.symm.trans found)
    exact .refl _
  case sub _ sub ih => exact (ih shape lookup).trans sub
  all_goals cases shape

def argumentQ : Expr := .record labelsQ (fun _ => .int 3)

private theorem argumentQ_not_typed {Θ : LocTypes} {Γ : VarTypes} :
    ¬ HasType Θ Γ argumentQ typeP := by
  intro typed
  obtain ⟨source, introType, subtype⟩ := typed.valueTyping (.record (fun _ => .int 3))
  cases introType with
  | record =>
    obtain ⟨_, _, same, fields⟩ := L3Subty.record_inv (labels := labelsP) subtype
    cases same
    obtain ⟨i, labelEq, _⟩ := fields 0
    have only : i = 0 := Fin.ext (Nat.le_zero.mp (Nat.le_of_lt_succ i.isLt))
    subst i
    exact (by decide : "q" ≠ "p") labelEq

/-- Exercise 32(3) on p. 88. Only the first argument omits the required field. -/
def missingFieldArgumentFunction : Expr :=
  .lam (.arr typeP .int)
    (.binary (.app (.bvar 0) argumentQ) .add
      (.app (.bvar 0) (.record labelsP (fun _ => .int 4))))

theorem missingFieldArgumentFunction_untypable (T : Ty) :
    ¬ HasType ∅ .empty missingFieldArgumentFunction T := by
  intro typed
  obtain ⟨_, introType, _⟩ := typed.valueTyping (.lam _ _)
  cases introType with
  | lam bodyTyped =>
    have left := add_left_typed bodyTyped rfl
    obtain ⟨A, B, fn, arg⟩ := app_typed left rfl
    have functionSubtype : L3Subty (.arr typeP .int) (.arr A B) := bound_subtype fn rfl rfl
    obtain ⟨_, _, same, domainSubtype, _⟩ := L3Subty.arr_inv functionSubtype
    cases same
    exact argumentQ_not_typed (.sub arg domainSubtype)

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
