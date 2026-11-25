module

public import Silmaril.Courses.Cambridge.L3.Denotation.SingleCall

/-! # A stored closure observes an argument's update to the current store -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation.SingleCall.Examples

private def createCell : Expr :=
  .ref (.lam .int (.binary (.bvar 1) .add (.binary (.bvar 0) .add (.deref (.loc 0)))))

private def argument : Expr := .seq (.assign (.loc 0) (.int 9)) (.int 1)

private def invoke : Expr := .app (.deref (.bvar 0)) argument

/-- Capture 7, allocate a function cell, read the function back, and call it.
The argument sets location 0 to 9. The function returns 7 + (1 + !0). -/
@[no_expose] def program : Expr := .letE .int (.int 7) (.letE (.ref (.arr .int .int)) createCell invoke)

private def capturedBody : Expr :=
  .binary (.int 7) .add (.binary (.bvar 0) .add (.deref (.loc 0)))

private def closure : Value := ⟨.lam .int capturedBody, .lam _ _⟩

private def lexical : Environment := Environment.empty.extend (integer 7)

private def afterAllocation (s : Store) (a : Loc) : Store := s.insert a closure

/-- The selected function cell stays allocated and the argument's write persists. -/
@[no_expose] def finalStore (s : Store) (a : Loc) : Store := (afterAllocation s a).insert 0 (integer 9)

private theorem create_returns {s t : Store} {v : Value} :
    Returns (Denotation.denoteWith lexical createCell) s v t ↔
      ∃ a, a ∉ s ∧ v = address a ∧ t = afterAllocation s a := by
  change Returns (pure closure >>= allocate) s v t ↔ _
  rw [pure_bind]
  change (∃ a, a ∉ s ∧ (v, t) = (address a, s.insert a closure)) ↔ _
  simp only [Prod.mk.injEq, afterAllocation]

private theorem function_returns {s t : Store} {v : Value} (a : Loc) :
    Returns (Denotation.denoteWith (lexical.extend (address a)) (.deref (.bvar 0)))
        (afterAllocation s a) v t ↔
      v = closure ∧ t = afterAllocation s a := by
  change Returns (pure (address a) >>= read) (afterAllocation s a) v t ↔ _
  rw [pure_bind]
  change ((afterAllocation s a).lookup a = some v ∧ t = afterAllocation s a) ↔ _
  rw [show (afterAllocation s a).lookup a = some closure from by simp [afterAllocation]]
  simp only [Option.some.injEq, eq_comm]

private theorem argument_returns {env : Environment} {s t : Store} {v : Value}
    (present : 0 ∈ s) :
    Returns (Denotation.denoteWith env argument) s v t ↔
      v = integer 1 ∧ t = s.insert 0 (integer 9) := by
  simp only [argument, Denotation.denoteWith, assign, address, pure_bind, returns_bind]
  constructor
  · rintro ⟨status, middle, written, returned⟩
    change 0 ∈ s ∧ (status, middle) = (unit, s.insert 0 (integer 9)) at written
    obtain ⟨_, equal⟩ := written
    cases equal
    exact (returns_pure _ _ _ _).mp returned
  · intro returned
    exact ⟨unit, s.insert 0 (integer 9), ⟨present, rfl⟩,
      (returns_pure _ _ _ _).mpr returned⟩

private theorem body_returns {s t : Store} {v : Value} (updated : s.lookup 0 = some (integer 9)) :
    Returns (applyClosure closure (integer 1)) s v t ↔ v = integer 17 ∧ t = s := by
  have computed :
      applyClosure closure (integer 1) =
        read (address 0) >>= fun r => binary .add (integer 1) r >>= binary .add (integer 7) := by
    simp only [applyClosure, closure, capturedBody, Denotation.denoteWith,
      Environment.extend, Binding.denote, pure_bind, bind_assoc]
  rw [computed, returns_bind]
  constructor
  · rintro ⟨readValue, middle, loaded, returned⟩
    change (s.lookup 0 = some readValue ∧ middle = s) at loaded
    rw [updated] at loaded
    obtain ⟨equal, sameStore⟩ := loaded
    subst middle
    have sameValue := Option.some.inj equal
    subst readValue
    change Returns (pure (integer 10) >>= binary .add (integer 7)) s v t at returned
    rw [pure_bind] at returned
    exact (returns_pure _ _ _ _).mp returned
  · intro returned
    refine ⟨integer 9, s, ⟨updated, rfl⟩, ?_⟩
    change Returns (pure (integer 10) >>= binary .add (integer 7)) s v t
    rw [pure_bind]
    exact (returns_pure _ _ _ _).mpr returned

private theorem invoke_returns {s t : Store} {v : Value} (a : Loc) (present : 0 ∈ s) :
    Returns (denoteWith (lexical.extend (address a)) invoke) (afterAllocation s a) v t ↔
      v = integer 17 ∧ t = finalStore s a := by
  simp only [invoke, denoteWith, returns_bind]
  have retained : 0 ∈ afterAllocation s a := Finmap.mem_insert.mpr (.inr present)
  have updated : (finalStore s a).lookup 0 = some (integer 9) := by simp [finalStore]
  constructor
  · rintro ⟨f, afterRead, loaded, arg, afterWrite, evaluated, called⟩
    obtain ⟨sameClosure, sameStore⟩ := (function_returns a).mp loaded
    subst f afterRead
    obtain ⟨sameArgument, updatedStore⟩ := (argument_returns retained).mp evaluated
    subst arg afterWrite
    exact (body_returns updated).mp called
  · intro returned
    exact ⟨closure, afterAllocation s a, (function_returns a).mpr ⟨rfl, rfl⟩,
      integer 1, finalStore s a, (argument_returns retained).mpr ⟨rfl, rfl⟩,
      (body_returns updated).mpr returned⟩

/-- Every choice outside the initial store returns the same integer and a
distinct function-cell binding. The initial store must allocate location 0. -/
theorem program_returns_iff {s t : Store} {v : Value} (present : 0 ∈ s) :
    Returns (denote program) s v t ↔
      ∃ a, a ∉ s ∧ v = integer 17 ∧ t = finalStore s a := by
  change Returns (pure (integer 7) >>= fun value =>
    denoteWith (Environment.empty.extend value) (.letE (.ref (.arr .int .int)) createCell invoke))
    s v t ↔ _
  rw [pure_bind]
  change Returns (Denotation.denoteWith lexical createCell >>= fun cell =>
    denoteWith (lexical.extend cell) invoke) s v t ↔ _
  rw [returns_bind]
  constructor
  · rintro ⟨cell, middle, allocated, invoked⟩
    obtain ⟨a, fresh, sameCell, sameStore⟩ := create_returns.mp allocated
    subst cell middle
    exact ⟨a, fresh, (invoke_returns a present).mp invoked⟩
  · rintro ⟨a, fresh, invoked⟩
    exact ⟨address a, afterAllocation s a, create_returns.mpr ⟨a, fresh, rfl, rfl⟩,
      (invoke_returns a present).mpr invoked⟩

theorem program_admitted (s : Store) : Admitted Environment.empty s program := by
  unfold program
  refine .letE (.value (.int 7)) ?_
  intro bias middle evaluated
  change Returns (pure (integer 7)) s bias middle at evaluated
  obtain ⟨sameBias, sameStore⟩ := (returns_pure _ _ _ _).mp evaluated
  subst bias middle
  refine .letE (Fragment.ref (.value (.lam _ _))) ?_
  intro cell middle allocated
  obtain ⟨a, _, sameCell, sameStore⟩ := create_returns.mp allocated
  subst cell middle
  unfold invoke
  refine .app (.deref (.bvar 0)) ?_ ?_
  · exact .seq (.assign (.value (.loc 0)) (.value (.int 9))) (.value (.int 1))
  · intro A body afterRead loaded
    have sameClosure := ((function_returns a).mp loaded).1
    have sameBody := (Expr.lam.inj (congrArg Subtype.val sameClosure)).2
    rw [sameBody]
    exact .binary (.value (.int 7)) (.binary (.bvar 0) (.deref (.value (.loc 0))))

theorem program_typed {Θ : LocTypes} (counter : Θ.lookup 0 = some .int) :
    HasType Θ .empty program .int :=
  .letE (.int 7)
    (.letE (.ref (.lam (.add (.bvar rfl) (.add (.bvar rfl) (.deref (.loc counter))))))
      (.app (.deref (.bvar rfl)) (.seq (.assign (.loc counter) (.int 9)) (.int 1))))

/-- Complete characterization of finite source returns, with concrete
allocation addresses and the complete final store. -/
theorem program_steps_iff {s t : Store} {v : Value} (present : 0 ∈ s) :
    Steps ⟨program, s⟩ ⟨v.val, t⟩ ↔
      ∃ a, a ∉ s ∧ v = integer 17 ∧ t = finalStore s a :=
  (adequate (program_admitted s)).symm.trans (program_returns_iff present)

private def initial : Store := (∅ : Store).insert 0 (integer 3)

private def initialTypes : LocTypes := (∅ : LocTypes).insert 0 .int

private theorem initial_typed : StoreTyped initialTypes initial := by
  constructor
  · intro loc
    simp only [initialTypes, initial, Finmap.mem_insert, Finmap.notMem_empty, or_false]
  · intro loc T v typeFound valueFound
    by_cases same : loc = 0
    · subst loc
      have typeEq : T = .int := by simpa [initialTypes] using typeFound.symm
      have valueEq : v = integer 3 := by simpa [initial] using valueFound.symm
      subst T v
      exact .int 3
    · simp [initialTypes, Finmap.lookup_insert_of_ne, same] at typeFound

example : ∃ Θ', initialTypes.Extends Θ' ∧ HasType Θ' .empty (.int 17) .int ∧
    StoreTyped Θ' (finalStore initial 1) :=
  typed_return (program_admitted initial) (program_typed (by simp [initialTypes]))
    initial_typed ((program_returns_iff (by simp [initial])).mpr
      ⟨1, by simp [initial, Finmap.notMem_empty], rfl, rfl⟩)

-- The relation permits both cell addresses, with different complete returns.
example :
    Steps ⟨program, initial⟩ ⟨.int 17, finalStore initial 1⟩ ∧
    Steps ⟨program, initial⟩ ⟨.int 17, finalStore initial 2⟩ ∧
    finalStore initial 1 ≠ finalStore initial 2 := by
  have returnsAt (a : Loc) (fresh : a ∉ initial) :
      Steps ⟨program, initial⟩ ⟨.int 17, finalStore initial a⟩ :=
    (program_steps_iff (v := integer 17) (by simp [initial])).mpr ⟨a, fresh, rfl, rfl⟩
  refine ⟨returnsAt 1 (by simp [initial, Finmap.notMem_empty]),
    returnsAt 2 (by simp [initial, Finmap.notMem_empty]), ?_⟩
  intro same
  have found := congrArg (fun h : Store => h.lookup 1) same
  simp [finalStore, afterAllocation, initial, Finmap.lookup_insert_of_ne] at found

-- With initial value 3, using the store from before the argument would return 11.
example (s t : Store) (present : 0 ∈ s) : ¬ Returns (denote program) s (integer 11) t := by
  intro returned
  obtain ⟨_, _, result, _⟩ := (program_returns_iff present).mp returned
  have impossible : (11 : Int) = 17 := Expr.int.inj (congrArg Subtype.val result)
  contradiction

end Silmaril.Courses.Cambridge.L3.Denotation.SingleCall.Examples
