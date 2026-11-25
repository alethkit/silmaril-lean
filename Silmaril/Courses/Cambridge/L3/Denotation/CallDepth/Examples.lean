module

public import Silmaril.Courses.Cambridge.L3.Denotation.CallDepth

/-! # A stored closure calls a captured helper -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation.CallDepth.Examples

private def helperBody : Expr :=
  .letE (.ref .int) (.ref (.bvar 0)) (.deref (.bvar 0))

private def helper : Value := ⟨.lam .int helperBody, .lam _ _⟩

private def makeOuter : Expr :=
  .ref (.lam .int (.app (.bvar 1) (.binary (.bvar 0) .add (.int 1))))

private def callOuter : Expr := .app (.deref (.bvar 0)) (.int 3)

private def quotedBody : Expr :=
  .app helper.val (.binary (.bvar 0) .add (.int 1))

private def outer : Value := ⟨.lam .int quotedBody, .lam _ _⟩

/-- The stored closure calls its captured helper on one more than its
argument. The helper allocates its argument and reads the new cell. -/
@[no_expose] def program : Expr :=
  .letE (.arr .int .int) helper.val (.letE (.ref (.arr .int .int)) makeOuter callOuter)

private def outerStore (s : Store) (a : Loc) : Store := s.insert a outer

/-- The outer function cell and the helper's integer cell remain allocated. -/
@[no_expose] def finalStore (s : Store) (a b : Loc) : Store :=
  (outerStore s a).insert b (integer 4)

private theorem allocation_returns {value result : Value} {s t : Store} :
    Returns (allocate value) s result t ↔
      ∃ a, a ∉ s ∧ result = address a ∧ t = s.insert a value := by
  change (∃ a, a ∉ s ∧ (result, t) = (address a, s.insert a value)) ↔ _
  simp only [Prod.mk.injEq]

private theorem read_insert_returns {s t : Store} {a : Loc} {stored v : Value} :
    Returns (read (address a)) (s.insert a stored) v t ↔ v = stored ∧ t = s.insert a stored := by
  change ((s.insert a stored).lookup a = some v ∧ t = s.insert a stored) ↔ _
  simp only [Finmap.lookup_insert, Option.some.injEq, eq_comm]

private theorem helper_returns {s t : Store} {v : Value} :
    Returns (Denotation.denoteWith (Environment.empty.extend (integer 4)) helperBody) s v t ↔
      ∃ b, b ∉ s ∧ v = integer 4 ∧ t = s.insert b (integer 4) := by
  change Returns ((pure (integer 4) >>= allocate) >>= fun cell => pure cell >>= read) s v t ↔ _
  simp only [pure_bind, returns_bind, allocation_returns]
  constructor
  · rintro ⟨_, _, ⟨b, fresh, rfl, rfl⟩, loaded⟩
    exact ⟨b, fresh, read_insert_returns.mp loaded⟩
  · rintro ⟨b, fresh, loaded⟩
    exact ⟨address b, s.insert b (integer 4), ⟨b, fresh, rfl, rfl⟩, read_insert_returns.mpr loaded⟩

private theorem quoted_call :
    denoteWith 1 (Environment.empty.extend (integer 3)) quotedBody =
      Denotation.denoteWith (Environment.empty.extend (integer 4)) helperBody := by
  change (pure helper >>= fun fn =>
    (pure (integer 3) >>= fun n => pure (integer 1) >>= binary .add n) >>=
      applyBody Denotation.denoteWith fn) = _
  simp only [pure_bind]
  change (pure (integer 4) >>= applyBody Denotation.denoteWith helper) = _
  rw [pure_bind]
  rfl

private theorem program_computation (depth : Nat) :
    denote (depth + 1) program =
      (allocate outer >>= fun cell =>
        read cell >>= fun fn => applyBody (denoteWith depth) fn (integer 3)) := by
  change (pure helper >>= fun h =>
    denoteLayer (denoteWith depth) (Environment.empty.extend h)
      (.letE (.ref (.arr .int .int)) makeOuter callOuter)) = _
  rw [pure_bind]
  change ((pure outer >>= allocate) >>= fun cell =>
    (pure cell >>= read) >>= fun fn => pure (integer 3) >>= applyBody (denoteWith depth) fn) = _
  simp only [pure_bind]

private theorem outer_returns_iff (depth : Nat) {s t : Store} {v : Value} :
    Returns (denote (depth + 1) program) s v t ↔
      ∃ a, a ∉ s ∧ Returns (applyBody (denoteWith depth) outer (integer 3)) (outerStore s a) v t := by
  simp only [program_computation, returns_bind, allocation_returns]
  constructor
  · rintro ⟨_, _, ⟨a, fresh, rfl, rfl⟩, _, _, loaded, called⟩
    obtain ⟨rfl, rfl⟩ := read_insert_returns.mp loaded
    exact ⟨a, fresh, called⟩
  · rintro ⟨a, fresh, called⟩
    exact ⟨address a, outerStore s a, ⟨a, fresh, rfl, rfl⟩,
      outer, outerStore s a, read_insert_returns.mpr ⟨rfl, rfl⟩, called⟩

/-- Both choices are retained. The second address is fresh in the store
with the first allocated cell already present. -/
theorem program_returns_iff {s t : Store} {v : Value} :
    Returns (denote 2 program) s v t ↔
      ∃ a b, a ∉ s ∧ b ∉ s ∧ b ≠ a ∧ v = integer 4 ∧ t = finalStore s a b := by
  rw [outer_returns_iff 1]
  change (∃ a, a ∉ s ∧ Returns (denoteWith 1 (Environment.empty.extend (integer 3))
    quotedBody) (outerStore s a) v t) ↔ _
  simp only [quoted_call, helper_returns]
  constructor
  · rintro ⟨a, freshA, b, freshB, result, store⟩
    have fresh : b ≠ a ∧ b ∉ s := by
      simpa only [outerStore, Finmap.mem_insert, not_or] using freshB
    exact ⟨a, b, freshA, fresh.2, fresh.1, result, store⟩
  · rintro ⟨a, b, freshA, freshB, distinct, result, store⟩
    exact ⟨a, freshA, b,
      by simpa only [outerStore, Finmap.mem_insert, not_or] using And.intro distinct freshB,
      result, store⟩

/-- A single invocation cannot run the application in the outer body. -/
theorem program_one_call_no_return {s t : Store} {v : Value} :
    ¬ Returns (denote 1 program) s v t := by
  intro returned
  obtain ⟨_, _, called⟩ := (outer_returns_iff 0).mp returned
  exact not_returns_fail _ _ _ called

theorem program_admitted (s : Store) : Admitted 2 Environment.empty s program := by
  unfold program
  refine .letE (.value helper.property) ?_
  intro fn middle returned
  change Returns (pure helper) s fn middle at returned
  obtain ⟨sameFn, sameStore⟩ := (returns_pure _ _ _ _).mp returned
  subst fn middle
  refine .letE (.ref (.value (.lam _ _))) ?_
  intro cell middle allocated
  change Returns (pure outer >>= allocate) s cell middle at allocated
  rw [pure_bind] at allocated
  obtain ⟨a, _, rfl, rfl⟩ := allocation_returns.mp allocated
  refine .app (.deref (.bvar 0)) (.value (.int 3)) ?_
  intro A body afterFn argument afterArgument loaded _
  change Returns (pure (address a) >>= read) (outerStore s a) _ afterFn at loaded
  rw [pure_bind] at loaded
  have sameBody := (Expr.lam.inj (congrArg Subtype.val (read_insert_returns.mp loaded).1)).2
  rw [sameBody]
  refine .app (.value helper.property) (.binary (.bvar 0) (.value (.int 1))) ?_
  intro B nestedBody afterNestedFn nestedArg afterNestedArg selected _
  change Returns (pure helper) afterArgument _ afterNestedFn at selected
  have sameHelper := (Expr.lam.inj (congrArg Subtype.val ((returns_pure _ _ _ _).mp selected).1)).2
  rw [sameHelper]
  exact .lexical (.letE (.ref (.bvar 0)) (.deref (.bvar 0)))

theorem program_typed (Θ : LocTypes) : HasType Θ .empty program .int :=
  .letE (.lam (.letE (.ref (.bvar rfl)) (.deref (.bvar rfl))))
    (.letE (.ref (.lam (.app (.bvar rfl) (.add (.bvar rfl) (.int 1)))))
      (.app (.deref (.bvar rfl)) (.int 3)))

/-- The original L3 relation has exactly these finite returns. -/
theorem program_steps_iff {s t : Store} {v : Value} :
    Steps ⟨program, s⟩ ⟨v.val, t⟩ ↔
      ∃ a b, a ∉ s ∧ b ∉ s ∧ b ≠ a ∧ v = integer 4 ∧ t = finalStore s a b :=
  (adequate (program_admitted s)).symm.trans program_returns_iff

example : Steps ⟨program, ∅⟩ ⟨.int 4, finalStore ∅ 2 5⟩ :=
  (program_steps_iff (v := integer 4)).mpr
    ⟨2, 5, Finmap.notMem_empty, Finmap.notMem_empty, by decide, rfl, rfl⟩

example : ∃ Θ', HasType Θ' .empty (.int 4) .int ∧ StoreTyped Θ' (finalStore ∅ 5 2) := by
  have returned := program_returns_iff.mpr
    ⟨5, 2, Finmap.notMem_empty, Finmap.notMem_empty, by decide, rfl, rfl⟩
  obtain ⟨Θ', _, typed, store⟩ :=
    typed_return (program_admitted ∅) (program_typed ∅) StoreTyped.empty returned
  exact ⟨Θ', typed, store⟩

end Silmaril.Courses.Cambridge.L3.Denotation.CallDepth.Examples
