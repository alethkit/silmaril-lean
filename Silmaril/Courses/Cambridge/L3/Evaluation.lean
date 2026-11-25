module

public import Silmaril.Courses.Cambridge.L3.Concrete.Grammar
public import Silmaril.Courses.Cambridge.L3.TypeChecker
public import Silmaril.Courses.Cambridge.L3.Interpreter
public import Silmaril.Courses.Cambridge.L3.Metatheory.Preservation

/-! # Type-checked evaluation from Cambridge L3 surface bytes (Exercise 31) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

inductive EvaluationResult where
  | parseError
  | storeTypeError
  | expressionTypeError
  | evaluated (type : Ty) (outcome : FuelResult)

/-- Parse surface bytes, validate the supplied initial location typing, infer
the closed expression's type, and run the deterministic reducer with fuel. -/
def evaluate (bytes : ByteArray) (Θ : LocTypes) (store : Store) (fuel : Nat) : EvaluationResult :=
  match Concrete.parseResolved bytes with
  | none => .parseError
  | some expression =>
      if checkStore Θ store then
        match infer Θ .empty expression with
        | none => .expressionTypeError
        | some T => .evaluated T (runFuel fuel ⟨expression, store⟩)
      else .storeTypeError

theorem evaluate_eq_parseError_iff {bytes : ByteArray} {Θ : LocTypes} {store : Store}
    {fuel : Nat} :
    evaluate bytes Θ store fuel = .parseError ↔ Concrete.parseResolved bytes = none := by
  cases parsed : Concrete.parseResolved bytes with
  | none => simp [evaluate, parsed]
  | some expression =>
      by_cases valid : checkStore Θ store = true
      · cases found : infer Θ .empty expression <;> simp [evaluate, parsed, valid, found]
      · simp [evaluate, parsed, valid]

theorem evaluate_eq_storeTypeError_iff {bytes : ByteArray} {Θ : LocTypes} {store : Store}
    {fuel : Nat} :
    evaluate bytes Θ store fuel = .storeTypeError ↔
      (Concrete.parseResolved bytes).isSome = true ∧ ¬ StoreTyped Θ store := by
  cases parsed : Concrete.parseResolved bytes with
  | none => simp [evaluate, parsed]
  | some expression =>
      by_cases valid : checkStore Θ store = true
      · have typed := checkStore_eq_true_iff.mp valid
        cases found : infer Θ .empty expression <;> simp [evaluate, parsed, valid, typed, found]
      · simp [evaluate, parsed, valid, checkStore_eq_true_iff.not.mp valid]

theorem evaluate_eq_expressionTypeError_iff {bytes : ByteArray} {Θ : LocTypes} {store : Store}
    {fuel : Nat} :
    evaluate bytes Θ store fuel = .expressionTypeError ↔
      ∃ expression, Concrete.parseResolved bytes = some expression ∧
        StoreTyped Θ store ∧ ∀ T, ¬ HasType Θ .empty expression T := by
  cases parsed : Concrete.parseResolved bytes with
  | none => simp [evaluate, parsed]
  | some expression =>
      by_cases valid : checkStore Θ store = true
      · have typed := checkStore_eq_true_iff.mp valid
        cases found : infer Θ .empty expression <;>
          simp [evaluate, parsed, valid, typed, ← infer_eq_none_iff, found]
      · simp [evaluate, parsed, valid, checkStore_eq_true_iff.not.mp valid]

/-- The entry point runs exactly when the parser accepts and both typing
judgments hold. Error diagnostics are ordered by the pipeline. -/
theorem evaluate_eq_evaluated_iff {bytes : ByteArray} {Θ : LocTypes} {store : Store}
    {fuel : Nat} {T : Ty} {outcome : FuelResult} :
    evaluate bytes Θ store fuel = .evaluated T outcome ↔
      ∃ expression, Concrete.parseResolved bytes = some expression ∧
        StoreTyped Θ store ∧ HasType Θ .empty expression T ∧
        runFuel fuel ⟨expression, store⟩ = outcome := by
  constructor
  · unfold evaluate
    split
    · simp
    · rename_i expression parsed
      split
      · rename_i valid
        split
        · simp
        · intro equal
          cases equal
          exact ⟨expression, parsed, checkStore_eq_true_iff.mp valid, infer_sound _ (by assumption), rfl⟩
      · simp
  · rintro ⟨expression, parsed, typedStore, typed, rfl⟩
    simp [evaluate, parsed, checkStore_eq_true_iff.mpr typedStore, infer_complete typed]

/-- Well-typed initial configurations cannot yield the stuck outcome. This
also applies when the selected trace consumes the whole fuel budget. -/
theorem runFuel_ne_stuck {Θ : LocTypes} {initial stopped : Config} {T : Ty} {fuel : Nat}
    (typed : HasType Θ .empty initial.expr T) (store : StoreTyped Θ initial.store) :
    runFuel fuel initial ≠ .stuck stopped := by
  intro equal
  have spec := runFuel_spec fuel initial
  rw [equal] at spec
  obtain ⟨⟨_, _, trace⟩, blocked⟩ := spec
  exact safety trace.toSteps typed store blocked

theorem evaluate_ne_stuck {bytes : ByteArray} {Θ : LocTypes} {store : Store}
    {fuel : Nat} {T : Ty} {stopped : Config} :
    evaluate bytes Θ store fuel ≠ .evaluated T (.stuck stopped) := by
  intro equal
  obtain ⟨expression, _, typedStore, typed, ran⟩ := evaluate_eq_evaluated_iff.mp equal
  exact runFuel_ne_stuck typed typedStore ran

/-- A returned result follows a fuel-bounded selected trace, and therefore
an original L3 trace, and has the inferred type in the grown typed store. -/
theorem evaluate_returned {bytes : ByteArray} {Θ : LocTypes} {store final : Store}
    {fuel : Nat} {T : Ty} {value : Value}
    (result : evaluate bytes Θ store fuel = .evaluated T (.returned value final)) :
    ∃ expression, Concrete.parseResolved bytes = some expression ∧
      HasType Θ .empty expression T ∧ StoreTyped Θ store ∧
      (∃ n ≤ fuel, SelectedSteps n ⟨expression, store⟩ ⟨value.val, final⟩) ∧
      (∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty value.val T ∧ StoreTyped Θ' final) := by
  obtain ⟨expression, parsed, typedStore, typed, ran⟩ := evaluate_eq_evaluated_iff.mp result
  have spec := runFuel_spec fuel ⟨expression, store⟩
  rw [ran] at spec
  obtain ⟨n, bound, trace⟩ := spec
  exact ⟨expression, parsed, typed, typedStore, ⟨n, bound, trace⟩,
    preservation_steps trace.toSteps typed typedStore⟩

/-- A returning finite trace of the selected reducer is reproduced using
sufficient fuel whenever parsing and initial typing succeed. -/
theorem evaluate_of_selectedSteps {bytes : ByteArray} {Θ : LocTypes} {store final : Store}
    {n fuel : Nat} {expression : Expr} {T : Ty} {value : Value}
    (parsed : Concrete.parseResolved bytes = some expression)
    (typedStore : StoreTyped Θ store) (typed : HasType Θ .empty expression T)
    (trace : SelectedSteps n ⟨expression, store⟩ ⟨value.val, final⟩) (bound : n ≤ fuel) :
    evaluate bytes Θ store fuel = .evaluated T (.returned value final) :=
  evaluate_eq_evaluated_iff.mpr ⟨_, parsed, typedStore, typed, trace.runFuel_returned bound⟩

end Silmaril.Courses.Cambridge.L3
