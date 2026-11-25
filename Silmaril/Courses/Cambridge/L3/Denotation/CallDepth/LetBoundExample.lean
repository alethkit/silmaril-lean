module

public import Silmaril.Courses.Cambridge.L3.Denotation.CallDepth

/-! # A let-bound call returns the reference its continuation updates -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation.CallDepth.LetBoundExample

private def allocator : Value := ⟨.lam .int (.ref (.bvar 0)), .lam _ _⟩

private def call : Expr := .app allocator.val (.int 4)

private def continuation : Expr :=
  .seq (.assign (.bvar 0) (.int 5)) (.deref (.bvar 0))

/-- Bind the reference returned by a call, update it, then read it. -/
@[no_expose] def program : Expr := .letE (.ref .int) call continuation

private theorem continuation_lexical : Fragment continuation :=
  .seq (.assign (.bvar 0) (.value (.int 5))) (.deref (.bvar 0))

private theorem call_returns {s t : Store} {v : Value} :
    Returns (denoteWith 1 Environment.empty call .sequenced) s v t ↔
      ∃ a, a ∉ s ∧ v = address a ∧ t = s.insert a (integer 4) := by
  change Returns (pure allocator >>= fun fn =>
    pure (integer 4) >>= applyBody Denotation.denoteWith fn) s v t ↔ _
  simp only [pure_bind]
  change Returns (pure (integer 4) >>= allocate) s v t ↔ _
  rw [pure_bind]
  change (∃ a, a ∉ s ∧ (v, t) = (address a, s.insert a (integer 4))) ↔ _
  simp only [Prod.mk.injEq]

private theorem read_insert_returns {s t : Store} {a : Loc} {stored v : Value} :
    Returns (read (address a)) (s.insert a stored) v t ↔ v = stored ∧ t = s.insert a stored := by
  change ((s.insert a stored).lookup a = some v ∧ t = s.insert a stored) ↔ _
  simp only [Finmap.lookup_insert, Option.some.injEq, eq_comm]

private theorem continuation_returns {s t : Store} {v : Value} {a : Loc} :
    Returns (Denotation.denoteWith (Environment.empty.extend (address a)) continuation)
      (s.insert a (integer 4)) v t ↔ v = integer 5 ∧ t = s.insert a (integer 5) := by
  change Returns
    ((pure (address a) >>= fun lhs => assign lhs (pure (integer 5))) >>= fun status =>
      sequence status (pure (address a) >>= read)) (s.insert a (integer 4)) v t ↔ _
  simp only [pure_bind]
  change Returns ((pure (integer 5) >>= write (address a)) >>= fun status =>
    sequence status (read (address a))) (s.insert a (integer 4)) v t ↔ _
  rw [pure_bind, returns_bind]
  constructor
  · rintro ⟨status, middle, written, loaded⟩
    change a ∈ s.insert a (integer 4) ∧ (status, middle) =
      (unit, (s.insert a (integer 4)).insert a (integer 5)) at written
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj written.2
    simpa only [Finmap.insert_insert] using read_insert_returns.mp loaded
  · intro returned
    have present : a ∈ s.insert a (integer 4) := Finmap.mem_insert.mpr (.inl rfl)
    refine ⟨unit, (s.insert a (integer 4)).insert a (integer 5), ⟨present, rfl⟩, ?_⟩
    change Returns (read (address a)) ((s.insert a (integer 4)).insert a (integer 5)) v t
    rw [Finmap.insert_insert]
    exact read_insert_returns.mpr returned

/-- Every choice gives the same integer and updates exactly the cell allocated
by the initializer. Conversely every address fresh for the initial store works. -/
theorem program_returns_iff {s t : Store} {v : Value} :
    Returns (denote 1 program .sequenced) s v t ↔
      ∃ a, a ∉ s ∧ v = integer 5 ∧ t = s.insert a (integer 5) := by
  change Returns (denoteWith 1 Environment.empty call .sequenced >>= fun result =>
    denoteWith 1 (Environment.empty.extend result) continuation .sequenced) s v t ↔ _
  simp only [returns_bind, call_returns, denoteWith_of_fragment continuation_lexical 1 _ .sequenced]
  constructor
  · rintro ⟨_, _, ⟨a, fresh, rfl, rfl⟩, returned⟩
    exact ⟨a, fresh, continuation_returns.mp returned⟩
  · rintro ⟨a, fresh, returned⟩
    exact ⟨address a, s.insert a (integer 4), ⟨a, fresh, rfl, rfl⟩,
      continuation_returns.mpr returned⟩

theorem program_admitted (s : Store) : Admitted 1 Environment.empty s program .sequenced := by
  unfold program call
  refine .letBound (.app (.value allocator.property) (.value (.int 4)) ?_)
    (fun _ => .lexical continuation_lexical)
  intro A body middle arg afterArg fnReturned _
  change Returns (pure allocator) s _ middle at fnReturned
  have sameFn := ((returns_pure _ _ _ _).mp fnReturned).1
  have sameBody := (Expr.lam.inj (congrArg Subtype.val sameFn)).2
  rw [sameBody]
  exact .lexical (.ref (.bvar 0))

private theorem call_not_lexical : ¬ Fragment call := by
  intro fragment
  unfold call at fragment
  cases fragment with
  | value ready => cases ready

/-- No depth suffices in tail mode, because the call is a let initializer. -/
theorem program_not_admitted_tail (depth : Nat) (s : Store) :
    ¬ Admitted depth Environment.empty s program := by
  intro admitted
  unfold program at admitted
  cases admitted with
  | lexical fragment =>
    cases fragment with
    | value ready => cases ready
    | letE bound _ => exact call_not_lexical bound
  | letE bound _ => exact call_not_lexical bound

theorem program_typed (Θ : LocTypes) : HasType Θ .empty program .int :=
  .letE (.app (.lam (.ref (.bvar rfl))) (.int 4))
    (.seq (.assign (.bvar rfl) (.int 5)) (.deref (.bvar rfl)))

/-- Exact direct-rule returns from any initial store. -/
theorem program_steps_iff {s t : Store} {v : Value} :
    Steps ⟨program, s⟩ ⟨v.val, t⟩ ↔
      ∃ a, a ∉ s ∧ v = integer 5 ∧ t = s.insert a (integer 5) :=
  (adequate (program_admitted s)).symm.trans program_returns_iff

example (a : Loc) :
    Steps ⟨program, ∅⟩ ⟨.int 5, (∅ : Store).insert a (integer 5)⟩ :=
  (program_steps_iff (v := integer 5)).mpr ⟨a, Finmap.notMem_empty, rfl, rfl⟩

example (a : Loc) :
    ∃ Θ', HasType Θ' .empty (.int 5) .int ∧ StoreTyped Θ' ((∅ : Store).insert a (integer 5)) := by
  have returned := program_returns_iff.mpr ⟨a, Finmap.notMem_empty, rfl, rfl⟩
  obtain ⟨Θ', _, typed, store⟩ :=
    typed_return (program_admitted ∅) (program_typed ∅) StoreTyped.empty returned
  exact ⟨Θ', typed, store⟩

end Silmaril.Courses.Cambridge.L3.Denotation.CallDepth.LetBoundExample
