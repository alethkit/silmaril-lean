module

public import Silmaril.Courses.Cambridge.L3.Examples

/-! # Two reference examples from §5.3

Sewell, *Semantics of Programming Languages*, 12 February 2026, p. 75.
Two allocations in a pair produce distinct cells. Slide 197's function
reads itself from its own reference and sums the integers from 1 to 3.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Exercises.ReferenceWorkedExamples

def allocationPair : Expr := .pair (.ref (.int 0)) (.ref (.int 0))

def pairStore (a b : Loc) : Store :=
  ((∅ : Store).insert a Examples.zero).insert b Examples.zero

theorem allocationPair_typed : HasType ∅ .empty allocationPair (.prod (.ref .int) (.ref .int)) :=
  .pair (.ref (.int 0)) (.ref (.int 0))

private theorem ref_zero_step {s : Store} {target : Config} (step : Step ⟨.ref (.int 0), s⟩ target) :
    ∃ loc, loc ∉ s ∧ target = ⟨.loc loc, s.insert loc Examples.zero⟩ := by
  generalize source : (⟨.ref (.int 0), s⟩ : Config) = before at step
  cases step
  case refValue old value loc fresh =>
    have store : s = old := congrArg Config.store source
    have payload : value = Examples.zero :=
      Subtype.ext (Expr.ref.inj (congrArg Config.expr source)).symm
    cases store
    cases payload
    exact ⟨loc, fresh, rfl⟩
  case refStep inner => cases source; cases inner
  all_goals cases source

private theorem first_allocation {target : Config} (step : Step ⟨allocationPair, ∅⟩ target) :
    ∃ a : Loc, target = ⟨.pair (.loc a) (.ref (.int 0)), (∅ : Store).insert a Examples.zero⟩ := by
  cases step with
  | pairLeft step =>
    obtain ⟨a, _, same⟩ := ref_zero_step step
    cases same
    exact ⟨a, rfl⟩
  | pairRight ready _ => cases ready

private theorem second_allocation (a : Loc) {target : Config}
    (step : Step ⟨.pair (.loc a) (.ref (.int 0)), (∅ : Store).insert a Examples.zero⟩ target) :
    ∃ b : Loc, a ≠ b ∧ target = ⟨.pair (.loc a) (.loc b), pairStore a b⟩ := by
  cases step with
  | pairLeft step => cases step
  | pairRight _ step =>
    obtain ⟨b, fresh, same⟩ := ref_zero_step step
    cases same
    have different : a ≠ b := fun eq => fresh (Finmap.mem_insert.mpr (Or.inl eq.symm))
    exact ⟨b, different, rfl⟩

/-- The possible returns are exactly the pairs of distinct locations.
Each returned location contains zero. -/
theorem allocationPair_returns_iff (result : Config) :
    (Steps ⟨allocationPair, ∅⟩ result ∧ IsValue result.expr) ↔
      ∃ a b, a ≠ b ∧ result = ⟨.pair (.loc a) (.loc b), pairStore a b⟩ := by
  constructor
  · rintro ⟨trace, ready⟩
    rcases trace.cases_head with rfl | ⟨_, first, rest⟩
    · cases ready with | pair left _ => cases left
    obtain ⟨a, rfl⟩ := first_allocation first
    rcases rest.cases_head with rfl | ⟨_, second, rest⟩
    · cases ready with | pair _ right => cases right
    obtain ⟨b, different, rfl⟩ := second_allocation a second
    rcases rest.cases_head with rfl | ⟨_, step, _⟩
    · exact ⟨a, b, different, rfl⟩
    · cases step with
      | pairLeft step | pairRight _ step => cases step
  · rintro ⟨a, b, different, rfl⟩
    have fresh : b ∉ (∅ : Store).insert a Examples.zero := by
      rw [Finmap.mem_insert]
      exact fun h => h.elim (fun equal => different equal.symm) Finmap.notMem_empty
    exact ⟨.head (.pairLeft (.refValue Examples.zero Finmap.notMem_empty))
      (.single (.pairRight (.loc a) (.refValue Examples.zero fresh))), .pair (.loc a) (.loc b)⟩

abbrev intFunction : Ty := .arr .int .int

def sumBody (cell argument : Expr) : Expr :=
  .cond (.binary argument .ge (.int 1))
    (.binary argument .add (.app (.deref cell) (.binary argument .add (.int (-1)))))
    (.int 0)

private theorem sumBody_typed {Θ : LocTypes} {Γ : VarTypes} {cell arg : Expr}
    (reference : HasType Θ Γ cell (.ref intFunction)) (argument : HasType Θ Γ arg .int) :
    HasType Θ Γ (sumBody cell arg) .int :=
  .cond (.ge argument (.int 1))
    (.add argument (.app (.deref reference) (.add argument (.int (-1)))))
    (.int 0)

/-- The p. 75 source program uses assignment to tie the recursive knot. -/
def selfReference : Expr :=
  .letE (.ref intFunction) (.ref Examples.identityValue.val)
    (.seq (.assign (.bvar 0) (.lam .int (sumBody (.bvar 1) (.bvar 0))))
      (.app (.deref (.bvar 0)) (.int 3)))

theorem selfReference_typed : HasType ∅ .empty selfReference .int :=
  .letE (.ref (.lam (.bvar rfl))) (.seq
    (.assign (.bvar rfl) (.lam (sumBody_typed (.bvar rfl) (.bvar rfl))))
    (.app (.deref (.bvar rfl)) (.int 3)))

def selfValue (address : Loc) : Value :=
  ⟨.lam .int (sumBody (.loc address) (.bvar 0)), .lam _ _⟩

def selfStore (address : Loc) : Store := (∅ : Store).insert address (selfValue address)

theorem selfStore_typed (address : Loc) :
    StoreTyped ((∅ : LocTypes).insert address intFunction) (selfStore address) := by
  constructor
  · intro loc
    simp [selfStore, Finmap.mem_insert, Finmap.notMem_empty]
  · intro loc T value typeAt valueAt
    have same : loc = address := by
      by_contra different
      simp [Finmap.lookup_insert_of_ne _ different] at typeAt
    subst loc
    simp at typeAt
    subst T
    simp [selfStore] at valueAt
    subst value
    exact .lam (sumBody_typed (.loc (by simp)) (.bvar rfl))

private def applyCell (address : Loc) (argument : Expr) : Expr :=
  .app (.deref (.loc address)) argument

private theorem loadFunction (address : Loc) (arg : Expr) :
    Step ⟨applyCell address arg, selfStore address⟩
      ⟨.app (selfValue address).val arg, selfStore address⟩ :=
  .appLeft (.derefValue (by simp [selfStore]))

private def programSum : Nat → Int
  | 0 => 0
  | n + 1 => (n + 1 : Int) + programSum n

private theorem applyFunction_returns (address : Loc) (n : Nat) :
    Steps ⟨.app (selfValue address).val (.int n), selfStore address⟩
      ⟨.int (programSum n), selfStore address⟩ := by
  induction n with
  | zero => exact .head (.appFun (.int 0)) (.head (.ifStep (.ge 0 1 _)) (.single .ifFalse))
  | succ n ih =>
    have test : Step ⟨.binary (.int (n + 1)) .ge (.int 1), selfStore address⟩
        ⟨.bool true, selfStore address⟩ := by
      have trueGuard : decide ((n : Int) + 1 ≥ 1) = true := by simp
      simpa only [trueGuard] using Step.ge ((n : Int) + 1) 1 (selfStore address)
    have predStep : Step ⟨.binary (.int (n + 1)) .add (.int (-1)), selfStore address⟩
        ⟨.int n, selfStore address⟩ := by
      have predEq : (n : Int) + 1 + -1 = n := by omega
      simpa only [predEq] using Step.add ((n : Int) + 1) (-1) (selfStore address)
    have call : Steps ⟨applyCell address (.binary (.int (n + 1)) .add (.int (-1))), selfStore address⟩
        ⟨.int (programSum n), selfStore address⟩ :=
      .head (loadFunction address _) (.head (.appRight (selfValue address).property predStep) ih)
    let wrap : Config → Config := fun c => ⟨.binary (.int (n + 1)) .add c.expr, c.store⟩
    have lift (c d : Config) (step : Step c d) : Step (wrap c) (wrap d) := by
      obtain ⟨_, _⟩ := c
      obtain ⟨_, _⟩ := d
      exact .binaryRight (.int _) step
    have addition := Relation.ReflTransGen.lift wrap lift _ _ call
    exact .head (.appFun (.int _)) (.head (.ifStep test)
      (.head .ifTrue (addition.tail (.add _ _ _))))

/-- Any fresh address chosen from the empty store gives the trace on slide
197, with that address holding the self-referential function at the end. -/
theorem selfReference_returns (address : Loc) :
    Steps ⟨selfReference, ∅⟩ ⟨.int 6, selfStore address⟩ := by
  have allocate : Step ⟨.ref Examples.identityValue.val, ∅⟩
      ⟨.loc address, (∅ : Store).insert address Examples.identityValue⟩ :=
    .refValue Examples.identityValue Finmap.notMem_empty
  refine .head (.letStep allocate) (.head (.letValue (.loc address)) ?_)
  have assign : Step ⟨.assign (.loc address) (selfValue address).val,
      (∅ : Store).insert address Examples.identityValue⟩ ⟨.skip, selfStore address⟩ := by
    simpa only [selfStore, Finmap.insert_insert] using
      Step.assignValue (selfValue address) (s := (∅ : Store).insert address Examples.identityValue)
        (loc := address) (by simp)
  exact .head (.seqStep assign) (.head .seqSkip
    (.head (loadFunction address (.int 3)) (applyFunction_returns address 3)))

end Silmaril.Courses.Cambridge.L3.Exercises.ReferenceWorkedExamples
