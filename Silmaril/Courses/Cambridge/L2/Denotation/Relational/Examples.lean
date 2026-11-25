module

public import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Institution
import Silmaril.Courses.Cambridge.L2.Denotation.Operational

/-! # Recursive calls and loops with mutable stores -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.RelationalDenotation.Examples

def cell (n : Int) : Store := L1.Store.fromList [("l", n)]

private theorem cell_write (n m : Int) : (cell n).insert "l" m = cell m := by
  simp [cell, L1.Store.fromList, Finmap.insert_insert]

private theorem cell_read (n : Int) : L1.Store.lookup (cell n) "l" = some n := by
  simp [cell, L1.Store.fromList]

/-- The guard increments the cell before it tests it, including on exit. -/
def increment : Expr := .assign "l" (.binary (.deref "l") .add (.int 1))

def guard : Expr := .seq increment (.binary (.int 1) .ge (.deref "l"))

def loop : Expr := .loop guard increment

private theorem increment_returns (ρ : RuntimeEnv) (n : Int) :
    Returns ρ increment (cell n) .unit (cell (n + 1)) := by
  rw [← cell_write n (n + 1)]
  exact .assign (.add (.deref (cell_read n)) (.int 1))
    (Finmap.mem_of_lookup_eq_some (cell_read n))

theorem loop_returns : Returns [] loop (cell 0) .unit (cell 3) :=
  .whileTrue
    (.seq (increment_returns [] 0) (.ge (.int 1) (.deref (cell_read 1))))
    (increment_returns [] 1)
    (.whileFalse (.seq (increment_returns [] 2) (.ge (.int 1) (.deref (cell_read 3)))))

theorem loop_small_step : Steps ⟨loop, cell 0⟩ ⟨.skip, cell 3⟩ :=
  ((adequate loop (cell 0) _).mp ⟨.unit, loop_returns, rfl⟩).1

/-- The positive branch adds the captured integer to the current cell
before calling the same closure with a decremented argument. -/
def countdown : Expr :=
  .cond (.binary (.bvar 0) .ge (.int 1))
    (.seq (.assign "l" (.binary (.deref "l") .add (.bvar 2)))
      (.app (.bvar 1) (.binary (.bvar 0) .add (.int (-1)))))
    (.deref "l")

/-- Capture the current contents of the cell, write 10, then apply the recursive closure to 1. -/
def recursiveProgram : Expr :=
  .letE .int (.deref "l") (.letRecFun .int .int countdown
    (.seq (.assign "l" (.int 10)) (.app (.bvar 0) (.int 1))))

def recursiveValue : RuntimeValue := .recursive .int .int countdown [.int 3]

private theorem countdown_zero :
    Returns [.int 0, recursiveValue, .int 3] countdown (cell 13) (.int 13) (cell 13) :=
  .ifFalse (.ge (a := 0) (.var rfl) (.int 1)) (.deref (cell_read 13))

private theorem countdown_one :
    Returns [.int 1, recursiveValue, .int 3] countdown (cell 10) (.int 13) (cell 13) := by
  apply Returns.ifTrue (.ge (a := 1) (.var rfl) (.int 1))
  have update :
      Returns [.int 1, recursiveValue, .int 3] (.assign "l" (.binary (.deref "l") .add (.bvar 2)))
        (cell 10) .unit (cell 13) := by
    rw [← cell_write 10 13]
    exact .assign (.add (b := 3) (.deref (cell_read 10)) (.var rfl))
      (Finmap.mem_of_lookup_eq_some (cell_read 10))
  exact .seq update (.appRec (.var rfl) (.add (a := 1) (.var rfl) (.int (-1))) countdown_zero)

theorem recursive_returns :
    Returns [] recursiveProgram (cell 3) (.int 13) (cell 13) := by
  apply Returns.letE (.deref (cell_read 3))
  apply Returns.letRec
  have update : Returns [recursiveValue, .int 3] (.assign "l" (.int 10)) (cell 3) .unit (cell 10) := by
    rw [← cell_write 3 10]
    exact .assign (.int 10) (Finmap.mem_of_lookup_eq_some (cell_read 3))
  exact .seq update (.appRec (.var rfl) (.int 1) countdown_one)

theorem recursive_observation :
    OperationalInstitution.semantics.May ⟨recursiveProgram, cell 3⟩ (.returned ⟨.int 13, cell 13⟩) :=
  (sat_iff _ _).mp ⟨.int 13, recursive_returns, rfl⟩

theorem open_argument (s : Store) :
    Observes [.int 4] (.binary (.bvar 0) .add (.int 1)) s ⟨.int 5, s⟩ :=
  ⟨.int 5, .add (a := 4) (.var rfl) (.int 1), rfl⟩

/-- A missing location is stuck. -/
theorem missing_stuck : Stuck ⟨.deref "l", L1.Store.empty⟩ := by
  constructor
  · intro ready
    cases ready
  · intro next step
    cases step with
    | deref lookup => simp at lookup

def forever : Expr := .loop (.bool true) .skip

/-- This loop has an infinite operational trace. -/
theorem forever_diverges (s : Store) : InfiniteTrace Step ⟨forever, s⟩ := by
  let first : Config := ⟨forever, s⟩
  let second : Config := ⟨.cond (.bool true) (.seq .skip forever) .skip, s⟩
  let third : Config := ⟨.seq .skip forever, s⟩
  apply InfiniteTrace.coinduct (fun c => c = first ∨ c = second ∨ c = third) ?_ (Or.inl rfl)
  intro c member
  rcases member with equal | equal | equal
  · cases equal; exact ⟨second, .while, Or.inr (Or.inl rfl)⟩
  · cases equal; exact ⟨third, .ifTrue, Or.inr (Or.inr rfl)⟩
  · cases equal; exact ⟨first, .seqSkip, Or.inl rfl⟩

theorem missing_has_no_observation (target : Config) :
    ¬ Observes [] (.deref "l") L1.Store.empty target := by
  cases target
  rintro ⟨v, run, _⟩
  cases run with
  | deref lookup => simp at lookup

theorem forever_has_no_observation (s : Store) (target : Config) : ¬ Observes [] forever s target := by
  intro observed
  obtain ⟨path, ready⟩ := (adequate _ _ _).mp observed
  cases target
  exact (RightUnique.not_infinite_of_final Denotation.stepRightUnique path
    (value_terminal ready)) (forever_diverges s)

end Silmaril.Courses.Cambridge.L2.RelationalDenotation.Examples
