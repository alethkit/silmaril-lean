module

public import Silmaril.Courses.Cambridge.L3.Typing
public import Silmaril.Courses.Cambridge.L3.Reduction
public import Silmaril.Foundations.InfiniteTrace

/-! # Cambridge SPL slide 256

The source uses subtraction, so the decreasing counter implements negation
with core L3 integer addition, comparison and a recursive function. The
observation is a finite series of integer calls to one returned closure.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.StatefulFunctions

private def plus (a b : Expr) : Expr := .binary a .add b
private def ge (a b : Expr) : Expr := .binary a .ge b

-- Reduce the argument's absolute magnitude by one, accumulating its negation.
private def negBody (self arg : Expr) : Expr :=
  .cond (ge arg (.int 1))
    (plus (.app self (plus arg (.int (-1)))) (.int (-1)))
    (.cond (ge (.int (-1)) arg)
      (plus (.app self (plus arg (.int 1))) (.int 1)) (.int 0))

private def negCode : Expr := negBody (.bvar 1) (.bvar 0)
private def negClosure : Expr := negCode.recClosure .int .int

/-- Closed core L3 implementation of integer negation. -/
@[no_expose] def negate : Expr := .letRecFun .int .int negCode (.bvar 0)

private theorem negBody_typed {Θ : LocTypes} {Γ : VarTypes} {f x : Expr}
    (hf : HasType Θ Γ f (.arr .int .int)) (hx : HasType Θ Γ x .int) :
    HasType Θ Γ (negBody f x) .int :=
  .cond (.ge hx (.int 1)) (.add (.app hf (.add hx (.int (-1)))) (.int (-1)))
    (.cond (.ge (.int (-1)) hx) (.add (.app hf (.add hx (.int 1))) (.int 1)) (.int 0))

theorem negate_typed (Θ : LocTypes) (Γ : VarTypes) : HasType Θ Γ negate (.arr .int .int) :=
  .letRecFun (negBody_typed (.bvar rfl) (.bvar rfl)) (.bvar rfl)

-- Determinate stretches of the direct relation, used after the allocation.
private def Forced (before after : Config) : Prop :=
  Step before after ∧ ∀ next, Step before next → next = after

private abbrev Path := Relation.ReflTransGen Forced

private theorem Forced.in_frame {e e' : Expr} {s t : Store} (plug : Expr → Expr)
    (edge : Forced ⟨e, s⟩ ⟨e', t⟩)
    (lift : ∀ {a b : Expr} {u w : Store}, Step ⟨a, u⟩ ⟨b, w⟩ →
      Step ⟨plug a, u⟩ ⟨plug b, w⟩)
    (invert : ∀ next, Step ⟨plug e, s⟩ next →
      ∃ c, Step ⟨e, s⟩ c ∧ next = ⟨plug c.expr, c.store⟩) :
    Forced ⟨plug e, s⟩ ⟨plug e', t⟩ := by
  refine ⟨lift edge.1, ?_⟩
  intro next step
  obtain ⟨c, inner, rfl⟩ := invert next step
  rw [edge.2 _ inner]

private theorem value_no_step {e : Expr} {s : Store} {next : Config} (v : IsValue e) :
    ¬ Step ⟨e, s⟩ next := by
  induction v generalizing s next <;> intro step <;> cases step
  all_goals solve_by_elim

private theorem config_value_no_step {before after : Config} (v : IsValue before.expr) :
    ¬ Step before after := by
  cases before
  exact value_no_step v

private theorem Forced.appLeft {f f' a : Expr} {s t : Store}
    (edge : Forced ⟨f, s⟩ ⟨f', t⟩) : Forced ⟨.app f a, s⟩ ⟨.app f' a, t⟩ := by
  apply edge.in_frame (fun e => .app e a) Step.appLeft
  intro _ step
  cases step with
  | appLeft inner => exact ⟨_, inner, rfl⟩
  | appRight ready _ => exact (value_no_step ready edge.1).elim
  | appFun _ => exact (value_no_step (.lam _ _) edge.1).elim

private theorem Forced.appRight {f a a' : Expr} {s t : Store}
    (ready : IsValue f) (edge : Forced ⟨a, s⟩ ⟨a', t⟩) :
    Forced ⟨.app f a, s⟩ ⟨.app f a', t⟩ := by
  apply edge.in_frame (Expr.app f) (Step.appRight ready)
  intro _ step
  cases step with
  | appLeft inner => exact (value_no_step ready inner).elim
  | appRight _ inner => exact ⟨_, inner, rfl⟩
  | appFun arg => exact (value_no_step arg edge.1).elim

private theorem Forced.plusLeft {a a' b : Expr} {s t : Store}
    (edge : Forced ⟨a, s⟩ ⟨a', t⟩) : Forced ⟨plus a b, s⟩ ⟨plus a' b, t⟩ := by
  apply edge.in_frame (fun e => plus e b) Step.binaryLeft
  intro _ step
  cases step with
  | binaryLeft inner => exact ⟨_, inner, rfl⟩
  | binaryRight ready _ => exact (value_no_step ready edge.1).elim
  | add => exact (value_no_step (.int _) edge.1).elim

private theorem Forced.plusRight {a b b' : Expr} {s t : Store}
    (ready : IsValue a) (edge : Forced ⟨b, s⟩ ⟨b', t⟩) :
    Forced ⟨plus a b, s⟩ ⟨plus a b', t⟩ := by
  apply edge.in_frame (plus a) (Step.binaryRight ready)
  intro _ step
  cases step with
  | binaryLeft inner => exact (value_no_step ready inner).elim
  | binaryRight _ inner => exact ⟨_, inner, rfl⟩
  | add => exact (value_no_step (.int _) edge.1).elim

private theorem Forced.cond {c c' a b : Expr} {s t : Store}
    (edge : Forced ⟨c, s⟩ ⟨c', t⟩) :
    Forced ⟨.cond c a b, s⟩ ⟨.cond c' a b, t⟩ := by
  apply edge.in_frame (fun e => .cond e a b) Step.ifStep
  intro _ step
  cases step with
  | ifStep inner => exact ⟨_, inner, rfl⟩
  | ifTrue => exact (value_no_step (.bool true) edge.1).elim
  | ifFalse => exact (value_no_step (.bool false) edge.1).elim

private theorem Forced.seq {a a' b : Expr} {s t : Store}
    (edge : Forced ⟨a, s⟩ ⟨a', t⟩) :
    Forced ⟨.seq a b, s⟩ ⟨.seq a' b, t⟩ := by
  apply edge.in_frame (fun e => .seq e b) Step.seqStep
  intro _ step
  cases step with
  | seqStep inner => exact ⟨_, inner, rfl⟩
  | seqSkip => exact (value_no_step .skip edge.1).elim

private theorem Forced.assign {a : Loc} {b b' : Expr} {s t : Store}
    (edge : Forced ⟨b, s⟩ ⟨b', t⟩) :
    Forced ⟨.assign (.loc a) b, s⟩ ⟨.assign (.loc a) b', t⟩ := by
  apply edge.in_frame (Expr.assign (.loc a)) Step.assignRight
  intro _ step
  cases step with
  | assignLeft inner => exact (value_no_step (.loc a) inner).elim
  | assignRight inner => exact ⟨_, inner, rfl⟩
  | assignValue v _ => exact (value_no_step v.property edge.1).elim

private theorem Path.in_frame {e e' : Expr} {s t : Store} (plug : Expr → Expr)
    (lift : ∀ {a b : Expr} {u w : Store}, Forced ⟨a, u⟩ ⟨b, w⟩ →
      Forced ⟨plug a, u⟩ ⟨plug b, w⟩)
    (path : Path ⟨e, s⟩ ⟨e', t⟩) :
    Path ⟨plug e, s⟩ ⟨plug e', t⟩ :=
  path.lift (fun c => (⟨plug c.expr, c.store⟩ : Config)) (fun ⟨_, _⟩ ⟨_, _⟩ edge => lift edge)

private theorem Path.steps {before after : Config} (path : Path before after) : Steps before after :=
  Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ path

private theorem Path.returns_iff {before after final : Config} (path : Path before after)
    (readyAfter : IsValue after.expr) (readyFinal : IsValue final.expr) :
    Steps before final ↔ final = after := by
  constructor
  · intro trace
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rcases trace.cases_head with same | ⟨_, edge, _⟩
        · exact same.symm
        · exact (config_value_no_step readyAfter edge).elim
    | @head source next edge _ ih =>
        rcases trace.cases_head with rfl | ⟨other, stepped, rest⟩
        · exact (config_value_no_step readyFinal edge.1).elim
        · have same := edge.2 other stepped
          exact ih (same ▸ rest)
  · rintro rfl
    exact path.steps

private theorem Path.not_diverges {before after : Config} (path : Path before after)
    (ready : IsValue after.expr) : ¬ InfiniteTrace Step before := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro infinite
      obtain ⟨_, step, _⟩ := infinite.unfold
      exact config_value_no_step ready step
  | head forced _ ih =>
      intro infinite
      obtain ⟨next, step, rest⟩ := infinite.unfold
      exact ih (forced.2 next step ▸ rest)

private theorem forced_add (x y : Int) (s : Store) :
    Forced ⟨plus (.int x) (.int y), s⟩ ⟨.int (x + y), s⟩ := by
  refine ⟨.add x y s, fun next step => ?_⟩
  cases step with
  | add => rfl
  | binaryLeft inner | binaryRight _ inner => cases inner

private theorem forced_ge (x y : Int) (s : Store) :
    Forced ⟨ge (.int x) (.int y), s⟩ ⟨.bool (x ≥ y), s⟩ := by
  refine ⟨.ge x y s, fun next step => ?_⟩
  cases step with
  | ge => rfl
  | binaryLeft inner | binaryRight _ inner => cases inner

private theorem forced_ifTrue (yes no : Expr) (s : Store) :
    Forced ⟨.cond (.bool true) yes no, s⟩ ⟨yes, s⟩ := by
  refine ⟨.ifTrue, fun next step => ?_⟩
  cases step with
  | ifTrue => rfl
  | ifStep inner => cases inner

private theorem forced_ifFalse (yes no : Expr) (s : Store) :
    Forced ⟨.cond (.bool false) yes no, s⟩ ⟨no, s⟩ := by
  refine ⟨.ifFalse, fun next step => ?_⟩
  cases step with
  | ifFalse => rfl
  | ifStep inner => cases inner

private theorem forced_appFun {A : Ty} {body arg : Expr} (ready : IsValue arg) (s : Store) :
    Forced ⟨.app (.lam A body) arg, s⟩ ⟨body.beta arg, s⟩ := by
  refine ⟨.appFun ready, fun next step => ?_⟩
  cases step with
  | appFun => rfl
  | appLeft inner => cases inner
  | appRight _ inner => exact (value_no_step ready inner).elim

private theorem forced_letRec (A B : Ty) (body continuation : Expr) (s : Store) :
    Forced ⟨.letRecFun A B body continuation, s⟩ ⟨continuation.beta (body.recClosure A B), s⟩ :=
  ⟨.letRecFun, fun _ step => by cases step; rfl⟩

private theorem forced_letValue {A : Ty} {value body : Expr} (ready : IsValue value) (s : Store) :
    Forced ⟨.letE A value body, s⟩ ⟨body.beta value, s⟩ := by
  refine ⟨.letValue ready, fun next step => ?_⟩
  cases step with
  | letValue => rfl
  | letStep inner => exact (value_no_step ready inner).elim

private theorem negClosure_value : IsValue negClosure := .lam _ _

private theorem neg_unfold (n : Int) (s : Store) :
    Path ⟨.app negClosure (.int n), s⟩ ⟨negBody negClosure (.int n), s⟩ := by
  change Path ⟨.app (.lam .int _) (.int n), s⟩ _
  refine .head (forced_appFun (.int n) s) ?_
  exact .single (forced_letRec .int .int negCode (negBody (.bvar 0) (.int n)) s)

private theorem negClosure_path (n : Int) (s : Store) :
    Path ⟨.app negClosure (.int n), s⟩ ⟨.int (-n), s⟩ := by
  refine (neg_unfold n s).trans ?_
  let up := plus (.app negClosure (plus (.int n) (.int (-1)))) (.int (-1))
  let down := plus (.app negClosure (plus (.int n) (.int 1))) (.int 1)
  let otherwise := Expr.cond (ge (.int (-1)) (.int n)) down (.int 0)
  have test := (forced_ge n 1 s).cond (a := up) (b := otherwise)
  by_cases pos : n ≥ 1
  · simp only [pos, decide_true] at test
    apply Relation.ReflTransGen.head test
    apply Relation.ReflTransGen.head (forced_ifTrue up otherwise s)
    have recursive := (negClosure_path (n + -1) s).in_frame (fun e => plus e (.int (-1)))
      (fun edge => edge.plusLeft)
    have head := ((forced_add n (-1) s).appRight negClosure_value).plusLeft (b := .int (-1))
    have result : -(n + -1) + -1 = -n := by omega
    exact (recursive.head head).tail (result ▸ forced_add (-(n + -1)) (-1) s)
  · simp only [pos, decide_false] at test
    apply Relation.ReflTransGen.head test
    apply Relation.ReflTransGen.head (forced_ifFalse up otherwise s)
    have test := (forced_ge (-1) n s).cond (a := down) (b := .int 0)
    by_cases negative : (-1 : Int) ≥ n
    · simp only [negative, decide_true] at test
      apply Relation.ReflTransGen.head test
      apply Relation.ReflTransGen.head (forced_ifTrue down (.int 0) s)
      have recursive := (negClosure_path (n + 1) s).in_frame (fun e => plus e (.int 1))
        (fun edge => edge.plusLeft)
      have head := ((forced_add n 1 s).appRight negClosure_value).plusLeft (b := .int 1)
      have result : -(n + 1) + 1 = -n := by omega
      exact (recursive.head head).tail (result ▸ forced_add (-(n + 1)) 1 s)
    · simp only [negative, decide_false] at test
      have zero : n = 0 := by omega
      rw [zero]
      exact .head test (.single (forced_ifFalse down (.int 0) s))
termination_by n.natAbs
decreasing_by all_goals omega

private theorem negate_after {argument : Expr} {s t : Store} {n : Int}
    (compute : Path ⟨argument, s⟩ ⟨.int n, t⟩) :
    Path ⟨.app negate argument, s⟩ ⟨.int (-n), t⟩ :=
  ((compute.in_frame (Expr.app negClosure) (fun edge => edge.appRight negClosure_value)).trans
    (negClosure_path n t)).head ((forced_letRec .int .int negCode (.bvar 0) s).appLeft)

private theorem negate_path (n : Int) (s : Store) :
    Path ⟨.app negate (.int n), s⟩ ⟨.int (-n), s⟩ :=
  negate_after .refl

theorem negate_returns_iff (n : Int) (s : Store) (final : Config) (ready : IsValue final.expr) :
    Steps ⟨.app negate (.int n), s⟩ final ↔ final = ⟨.int (-n), s⟩ :=
  (negate_path n s).returns_iff (.int _) ready


/-- The two private representations of the running total. -/
inductive Direction where
  | increasing
  | decreasing

def Direction.contents : Direction → Int → Int
  | .increasing, n => n
  | .decreasing, n => -n

def cell (s : Store) (a : Loc) (contents : Int) : Store :=
  s.insert a ⟨.int contents, .int contents⟩

theorem cell_lookup (s : Store) (a : Loc) (n : Int) :
    (cell s a n).lookup a = some ⟨.int n, .int n⟩ :=
  Finmap.lookup_insert _

theorem cell_lookup_other (s : Store) (a b : Loc) (n : Int) (different : b ≠ a) :
    (cell s a n).lookup b = s.lookup b :=
  Finmap.lookup_insert_of_ne s different

private def counterBody (d : Direction) (ref arg : Expr) : Expr :=
  match d with
  | .increasing => .seq (.assign ref (plus (.deref ref) arg)) (.deref ref)
  | .decreasing =>
      .seq (.assign ref (plus (.deref ref) (.app negate arg))) (.app negate (.deref ref))

/-- The slide's function maker, with the reference bound outside the lambda. -/
@[no_expose] def counter (d : Direction) : Expr :=
  .letE (.ref .int) (.ref (.int 0)) (.lam .int (counterBody d (.bvar 1) (.bvar 0)))

/-- Result of choosing a particular private address during initialization. -/
@[no_expose] def closure (d : Direction) (a : Loc) : Expr :=
  .lam .int (counterBody d (.loc a) (.bvar 0))

theorem counter_typed (d : Direction) (Θ : LocTypes) :
    HasType Θ .empty (counter d) (.arr .int .int) := by
  cases d
  · exact .letE (.ref (.int 0)) (.lam (.seq
      (.assign (.bvar rfl) (.add (.deref (.bvar rfl)) (.bvar rfl)))
      (.deref (.bvar rfl))))
  · exact .letE (.ref (.int 0)) (.lam (.seq
      (.assign (.bvar rfl) (.add (.deref (.bvar rfl))
        (.app (negate_typed _ _) (.bvar rfl))))
      (.app (negate_typed _ _) (.deref (.bvar rfl)))))

private def allocated (d : Direction) (s : Store) (a : Loc) : Config :=
  ⟨.letE (.ref .int) (.loc a) (.lam .int (counterBody d (.bvar 1) (.bvar 0))), cell s a 0⟩

private theorem allocate (d : Direction) (s : Store) (a : Loc) (fresh : a ∉ s) :
    Step ⟨counter d, s⟩ (allocated d s a) :=
  .letStep (.refValue ⟨.int 0, .int 0⟩ fresh)

private theorem allocate_only {d : Direction} {s : Store} {next : Config}
    (step : Step ⟨counter d, s⟩ next) :
    ∃ a, a ∉ s ∧ next = allocated d s a := by
  change Step ⟨.letE (.ref .int) (.ref (.int 0)) _, s⟩ next at step
  cases step with
  | letValue value => cases value
  | letStep allocate =>
      generalize number : Expr.int 0 = source at allocate
      cases allocate with
      | refStep inner =>
          rw [← number] at inner
          cases inner
      | refValue value fresh =>
          have same : value = ⟨.int 0, .int 0⟩ := Subtype.ext number.symm
          cases same
          exact ⟨_, fresh, rfl⟩

private theorem initialized (d : Direction) (s : Store) (a : Loc) :
    Path (allocated d s a) ⟨closure d a, cell s a 0⟩ := by
  cases d <;> exact .single (forced_letValue (.loc a) _)

/-- Every initialization return corresponds to exactly a permitted fresh
address and leaves a zero cell at that address. -/
theorem counter_returns_iff (d : Direction) (s : Store) (final : Config)
    (ready : IsValue final.expr) :
    Steps ⟨counter d, s⟩ final ↔
      ∃ a, a ∉ s ∧ final = ⟨closure d a, cell s a 0⟩ := by
  constructor
  · intro trace
    rcases trace.cases_head with equal | ⟨_, edge, rest⟩
    · rw [← equal] at ready
      unfold counter at ready
      cases ready
    · obtain ⟨a, fresh, rfl⟩ := allocate_only edge
      exact ⟨a, fresh, ((initialized d s a).returns_iff (.lam _ _) ready).mp rest⟩
  · rintro ⟨a, fresh, rfl⟩
    exact (initialized d s a).steps.head (allocate d s a fresh)

private theorem forced_read (s : Store) (a : Loc) (n : Int) :
    Forced ⟨.deref (.loc a), cell s a n⟩ ⟨.int n, cell s a n⟩ := by
  have found := cell_lookup s a n
  refine ⟨.derefValue found, fun next step => ?_⟩
  cases step with
  | derefStep inner => cases inner
  | derefValue lookup =>
      cases Option.some.inj (lookup.symm.trans found)
      rfl

private theorem forced_write (s : Store) (a : Loc) (old n : Int) :
    Forced ⟨.assign (.loc a) (.int n), cell s a old⟩ ⟨.skip, cell s a n⟩ := by
  have present : a ∈ cell s a old := Finmap.mem_insert.mpr (Or.inl rfl)
  constructor
  · simpa only [cell, Finmap.insert_insert] using Step.assignValue (⟨.int n, .int n⟩ : Value) present
  · intro next step
    generalize number : Expr.int n = rhs at step
    cases step with
    | assignLeft inner => cases inner
    | assignRight inner =>
        rw [← number] at inner
        cases inner
    | assignValue value _ =>
        have same : value = ⟨.int n, .int n⟩ := Subtype.ext number.symm
        cases same
        simp only [cell, Finmap.insert_insert]

private theorem forced_seqSkip (e : Expr) (s : Store) :
    Forced ⟨.seq .skip e, s⟩ ⟨e, s⟩ := by
  refine ⟨.seqSkip, fun _ step => ?_⟩
  cases step with
  | seqSkip => rfl
  | seqStep inner => cases inner

private theorem write_then (s : Store) (a : Loc) (old new : Int) (rhs next : Expr)
    (compute : Path ⟨rhs, cell s a old⟩ ⟨.int new, cell s a old⟩) :
    Path ⟨.seq (.assign (.loc a) rhs) next, cell s a old⟩ ⟨next, cell s a new⟩ :=
  ((compute.in_frame (fun e => .seq (.assign (.loc a) e) next)
    (fun edge => edge.assign.seq)).tail (forced_write s a old new).seq).tail
    (forced_seqSkip next (cell s a new))

private theorem add_read (s : Store) (a : Loc) (old n : Int) (arg : Expr)
    (compute : Path ⟨arg, cell s a old⟩ ⟨.int n, cell s a old⟩) :
    Path ⟨plus (.deref (.loc a)) arg, cell s a old⟩ ⟨.int (old + n), cell s a old⟩ :=
  ((compute.in_frame (plus (.int old)) (fun edge => edge.plusRight (.int old))).head
    (forced_read s a old).plusLeft).tail (forced_add old n (cell s a old))

private theorem call_path (d : Direction) (s : Store) (a : Loc) (total n : Int) :
    Path ⟨.app (closure d a) (.int n), cell s a (d.contents total)⟩
      ⟨.int (total + n), cell s a (d.contents (total + n))⟩ := by
  cases d with
  | increasing =>
      have compute := add_read s a total n (.int n) .refl
      have written := write_then s a total (total + n) _ (.deref (.loc a)) compute
      exact (written.tail (forced_read s a (total + n))).head (forced_appFun (.int n) _)
  | decreasing =>
      have compute := add_read s a (-total) (-n) _ (negate_path n (cell s a (-total)))
      have sum : -total + -n = -(total + n) := by omega
      have written := write_then s a (-total) (-(total + n)) _ (.app negate (.deref (.loc a)))
        (sum ▸ compute)
      have loaded : Path ⟨.app negate (.deref (.loc a)), cell s a (-(total + n))⟩
          ⟨.int (total + n), cell s a (-(total + n))⟩ := by
        simpa only [Int.neg_neg] using
          negate_after (.single (forced_read s a (-(total + n))))
      have ready := written.trans loaded
      change Path ⟨.app (.lam .int _) (.int n), _⟩ _
      exact ready.head (forced_appFun (.int n) _)

/-- The response is the updated total in both representations. The final
store preserves the frame, and the private cell holds the signed total. -/
theorem call_returns_iff (d : Direction) (s : Store) (a : Loc) (total n : Int)
    (final : Config) (ready : IsValue final.expr) :
    Steps ⟨.app (closure d a) (.int n), cell s a (d.contents total)⟩ final ↔
      final = ⟨.int (total + n), cell s a (d.contents (total + n))⟩ :=
  (call_path d s a total n).returns_iff (.int _) ready


theorem counter_not_diverges (d : Direction) (s : Store) :
    ¬ InfiniteTrace Step ⟨counter d, s⟩ := by
  intro infinite
  obtain ⟨_, first, rest⟩ := infinite.unfold
  obtain ⟨a, _, rfl⟩ := allocate_only first
  exact (initialized d s a).not_diverges (.lam _ _) rest

theorem call_not_diverges (d : Direction) (s : Store) (a : Loc) (total n : Int) :
    ¬ InfiniteTrace Step ⟨.app (closure d a) (.int n), cell s a (d.contents total)⟩ :=
  (call_path d s a total n).not_diverges (.int _)

/-- Call one initialized function on a finite list of integer values,
threading the actual store from one call to the next. -/
inductive Calls (fn : Expr) : Store → List Int → List Int → Store → Prop where
  | nil (s : Store) : Calls fn s [] [] s
  | cons {s middle final : Store} {arg out : Int} {args outs : List Int}
      (call : Steps ⟨.app fn (.int arg), s⟩ ⟨.int out, middle⟩)
      (rest : Calls fn middle args outs final) : Calls fn s (arg :: args) (out :: outs) final

def responses (total : Int) : List Int → List Int
  | [] => []
  | arg :: args => (total + arg) :: responses (total + arg) args

theorem calls_iff (d : Direction) (s : Store) (a : Loc) (total : Int)
    (args outs : List Int) (final : Store) :
    Calls (closure d a) (cell s a (d.contents total)) args outs final ↔
      outs = responses total args ∧ final = cell s a (d.contents (args.foldl (· + ·) total)) := by
  induction args generalizing total outs final with
  | nil =>
      constructor
      · intro run
        cases run
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact .nil _
  | cons arg args ih =>
      constructor
      · intro run
        cases run with
        | cons call rest =>
            have eq := (call_returns_iff d s a total arg _ (.int _)).mp call
            cases eq
            have exactRest := (ih (total + arg) _ _).mp rest
            exact ⟨congrArg (List.cons (total + arg)) exactRest.1, exactRest.2⟩
      · rintro ⟨rfl, rfl⟩
        exact .cons (call_path d s a total arg).steps
          ((ih (total + arg) _ _).mpr ⟨rfl, rfl⟩)

/-- Initialize the counter once, then reuse that particular closure. The
client supplies only integer values and observes the integer responses. -/
def Session (d : Direction) (s : Store) (args outs : List Int) (final : Store) : Prop :=
  ∃ initialized : Config, Steps ⟨counter d, s⟩ initialized ∧
    IsValue initialized.expr ∧ Calls initialized.expr initialized.store args outs final

theorem session_iff (d : Direction) (s : Store) (args outs : List Int) (final : Store) :
    Session d s args outs final ↔
      outs = responses 0 args ∧
        ∃ a, a ∉ s ∧ final = cell s a (d.contents (args.foldl (· + ·) 0)) := by
  constructor
  · rintro ⟨initial, trace, ready, calls⟩
    obtain ⟨a, fresh, rfl⟩ := (counter_returns_iff d s initial ready).mp trace
    have run := (calls_iff d s a 0 args outs final).mp (by cases d <;> exact calls)
    exact ⟨run.1, a, fresh, run.2⟩
  · rintro ⟨outputs, a, fresh, store⟩
    have calls := (calls_iff d s a 0 args outs final).mpr ⟨outputs, store⟩
    refine ⟨⟨closure d a, cell s a 0⟩,
      (counter_returns_iff d s _ (.lam _ _)).mpr ⟨a, fresh, rfl⟩, .lam _ _, ?_⟩
    cases d <;> exact calls

/-- Every chosen address produces the same response list in either
representation. At that address the final stores carry opposite totals. -/
theorem session_at {s : Store} {a : Loc} (fresh : a ∉ s) (d : Direction) (args : List Int) :
    Session d s args (responses 0 args) (cell s a (d.contents (args.foldl (· + ·) 0))) :=
  (session_iff d s args _ _).mpr ⟨rfl, a, fresh, rfl⟩

/-- The finite client observes exactly one response list, independently
of how either counter chooses its fresh address. -/
theorem responses_agree (s : Store) (args outs : List Int) :
    (∃ final, Session .increasing s args outs final) ↔
      (∃ final, Session .decreasing s args outs final) := by
  have observed (d : Direction) :
      (∃ final, Session d s args outs final) ↔ outs = responses 0 args := by
    constructor
    · rintro ⟨final, run⟩
      exact ((session_iff d s args outs final).mp run).1
    · rintro rfl
      exact ⟨_, session_at s.freshAddress_not_mem d args⟩
  exact (observed .increasing).trans (observed .decreasing).symm

-- The same observer can use negative, positive, and zero arguments.
example : Session .increasing ∅ [4, -6, 0, 3] [4, -2, -2, 1] (cell ∅ 2 1) :=
  session_at Finmap.notMem_empty .increasing [4, -6, 0, 3]

example : Session .decreasing ∅ [4, -6, 0, 3] [4, -2, -2, 1] (cell ∅ 5 (-1)) :=
  session_at Finmap.notMem_empty .decreasing [4, -6, 0, 3]

end Silmaril.Courses.Cambridge.L3.StatefulFunctions
