module

public import Silmaril.Courses.Cambridge.L3.Typing
public import Silmaril.Courses.Cambridge.L3.Reduction
public import Silmaril.Foundations.InfiniteTrace

/-! # Cambridge SPL slides 257–258

A local call-by-value fragment for the pointer-equality example in the
12 February 2026 notes (`sewell2026semantics`). The fragment keeps only the
forms needed for the two functions and their client. In particular, all
allocations are of `ref 0`, and closed core unit branches use core reduction.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.PointerEquality

inductive Term where
  | var (index : Nat)
  | letE (value body : Term)
  | lam (domain : Ty) (body : Term)
  | app (fn arg : Term)
  | refZero
  | ptrEq (left right : Term)
  | cond (test yes no : Term)
  | coreUnit (expr : L3.Expr)

inductive HasType : List Ty → Term → Ty → Prop where
  | var {Γ : List Ty} {i : Nat} {T : Ty} :
      Γ[i]? = some T → HasType Γ (.var i) T
  | letE {Γ : List Ty} {value body : Term} {A B : Ty} :
      HasType Γ value A → HasType (A :: Γ) body B → HasType Γ (.letE value body) B
  | lam {Γ : List Ty} {body : Term} {A B : Ty} :
      HasType (A :: Γ) body B → HasType Γ (.lam A body) (.arr A B)
  | app {Γ : List Ty} {fn arg : Term} {A B : Ty} :
      HasType Γ fn (.arr A B) → HasType Γ arg A → HasType Γ (.app fn arg) B
  | refZero {Γ : List Ty} : HasType Γ .refZero (.ref .int)
  | ptrEq {Γ : List Ty} {left right : Term} {T : Ty} :
      HasType Γ left (.ref T) → HasType Γ right (.ref T) → HasType Γ (.ptrEq left right) .bool
  | cond {Γ : List Ty} {test yes no : Term} {T : Ty} :
      HasType Γ test .bool → HasType Γ yes T → HasType Γ no T → HasType Γ (.cond test yes no) T
  | coreUnit {Γ : List Ty} {expr : L3.Expr} :
      L3.HasType ∅ .empty expr .unit → HasType Γ (.coreUnit expr) .unit

inductive Value where
  | address (loc : Loc)
  | bool (value : Bool)
  | unit
  | closure (body : Term) (captured : List Value)

def allocZero (s : Store) (a : Loc) : Store :=
  s.insert a ⟨.int 0, .int 0⟩

/-- Finite returns in the fragment. Application evaluates the function, then
the argument, then the body in the captured environment extended by that
argument. Equality evaluates both operands left to right and compares their
addresses without accessing the contents of either cell. -/
inductive Eval : List Value → Term → Store → Value → Store → Prop where
  | var {ρ : List Value} {i : Nat} {s : Store} {v : Value} :
      ρ[i]? = some v → Eval ρ (.var i) s v s
  | letE {ρ : List Value} {value body : Term} {s t u : Store} {v w : Value} :
      Eval ρ value s v t → Eval (v :: ρ) body t w u → Eval ρ (.letE value body) s w u
  | lam {ρ : List Value} {A : Ty} {body : Term} {s : Store} :
      Eval ρ (.lam A body) s (.closure body ρ) s
  | app {ρ captured : List Value} {fn arg body : Term} {s t u final : Store} {v w : Value} :
      Eval ρ fn s (.closure body captured) t → Eval ρ arg t v u →
      Eval (v :: captured) body u w final → Eval ρ (.app fn arg) s w final
  | refZero {ρ : List Value} {s : Store} {a : Loc} :
      a ∉ s → Eval ρ .refZero s (.address a) (allocZero s a)
  | ptrEq {ρ : List Value} {left right : Term} {s t u : Store} {a b : Loc} :
      Eval ρ left s (.address a) t → Eval ρ right t (.address b) u →
      Eval ρ (.ptrEq left right) s (.bool (decide (a = b))) u
  | cond {ρ : List Value} {test yes no : Term} {s t u : Store} {b : Bool} {v : Value} :
      Eval ρ test s (.bool b) t → Eval ρ (if b then yes else no) t v u →
      Eval ρ (.cond test yes no) s v u
  | coreUnit {ρ : List Value} {expr : L3.Expr} {s t : Store} :
      L3.Steps ⟨expr, s⟩ ⟨.skip, t⟩ → Eval ρ (.coreUnit expr) s .unit t

private theorem eval_var_iff {ρ : List Value} {i : Nat} {s t : Store} {v : Value} :
    Eval ρ (.var i) s v t ↔ ρ[i]? = some v ∧ t = s := by
  constructor
  · rintro ⟨lookup⟩
    exact ⟨lookup, rfl⟩
  · rintro ⟨lookup, rfl⟩
    exact .var lookup

private theorem eval_let_iff {ρ : List Value} {value body : Term} {s u : Store} {w : Value} :
    Eval ρ (.letE value body) s w u ↔ ∃ v t, Eval ρ value s v t ∧ Eval (v :: ρ) body t w u := by
  constructor
  · intro run
    cases run with
    | letE valueRun bodyRun => exact ⟨_, _, valueRun, bodyRun⟩
  · rintro ⟨_, _, valueRun, bodyRun⟩
    exact .letE valueRun bodyRun

private theorem eval_lam_iff {ρ : List Value} {A : Ty} {body : Term} {s t : Store} {v : Value} :
    Eval ρ (.lam A body) s v t ↔ v = .closure body ρ ∧ t = s := by
  constructor
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .lam

private theorem eval_app_iff {ρ : List Value} {fn arg : Term} {s final : Store} {w : Value} :
    Eval ρ (.app fn arg) s w final ↔
      ∃ body captured t v u, Eval ρ fn s (.closure body captured) t ∧
        Eval ρ arg t v u ∧ Eval (v :: captured) body u w final := by
  constructor
  · intro run
    cases run with
    | app fnRun argRun bodyRun => exact ⟨_, _, _, _, _, fnRun, argRun, bodyRun⟩
  · rintro ⟨_, _, _, _, _, fnRun, argRun, bodyRun⟩
    exact .app fnRun argRun bodyRun

theorem eval_refZero_iff {ρ : List Value} {s t : Store} {v : Value} :
    Eval ρ .refZero s v t ↔ ∃ a, a ∉ s ∧ v = .address a ∧ t = allocZero s a := by
  constructor
  · intro run
    cases run with
    | refZero fresh => exact ⟨_, fresh, rfl, rfl⟩
  · rintro ⟨_, fresh, rfl, rfl⟩
    exact .refZero fresh

theorem eval_ptrEq_iff {ρ : List Value} {left right : Term} {s u : Store} {v : Value} :
    Eval ρ (.ptrEq left right) s v u ↔
      ∃ a t b, Eval ρ left s (.address a) t ∧ Eval ρ right t (.address b) u ∧
        v = .bool (decide (a = b)) := by
  constructor
  · intro run
    cases run with
    | ptrEq leftRun rightRun => exact ⟨_, _, _, leftRun, rightRun, rfl⟩
  · rintro ⟨_, _, _, leftRun, rightRun, rfl⟩
    exact .ptrEq leftRun rightRun

private theorem eval_cond_iff {ρ : List Value} {test yes no : Term} {s u : Store} {v : Value} :
    Eval ρ (.cond test yes no) s v u ↔ ∃ b t, Eval ρ test s (.bool b) t ∧
      Eval ρ (if b then yes else no) t v u := by
  constructor
  · intro run
    cases run with
    | cond testRun branchRun => exact ⟨_, _, testRun, branchRun⟩
  · rintro ⟨_, _, testRun, branchRun⟩
    exact .cond testRun branchRun

private theorem eval_coreUnit_iff {ρ : List Value} {expr : L3.Expr} {s t : Store} {v : Value} :
    Eval ρ (.coreUnit expr) s v t ↔ v = .unit ∧ L3.Steps ⟨expr, s⟩ ⟨.skip, t⟩ := by
  constructor
  · intro run
    cases run with
    | coreUnit path => exact ⟨rfl, path⟩
  · rintro ⟨rfl, path⟩
    exact .coreUnit path

/-- The two functions differ only in which captured reference they test. -/
inductive Example where
  | f
  | g

private def testedAddress (which : Example) (x y : Loc) : Loc :=
  match which with
  | .f => x
  | .g => y

def functionBody (which : Example) : Term :=
  let tested := match which with
    | .f => 2
    | .g => 1
  .cond (.ptrEq (.var 0) (.var tested)) (.var 1) (.var 2)

/-- With indices ordered `[z, y, x]` in the lambda body, these are the two
closed functions on slide 258. -/
def maker (which : Example) : Term :=
  .letE .refZero (.letE .refZero (.lam (.ref .int) (functionBody which)))

/-- Bind the function once, call it on a freshly allocated cell, then
compare the first result with the result of calling it again on that result. -/
def probe (hole : Term) : Term :=
  .letE hole (.letE .refZero (.letE (.app (.var 1) (.var 0))
    (.ptrEq (.app (.var 2) (.var 0)) (.var 0))))

theorem maker_typed (which : Example) : HasType [] (maker which) (.arr (.ref .int) (.ref .int)) := by
  cases which <;> exact .letE .refZero (.letE .refZero (.lam (.cond
    (.ptrEq (.var rfl) (.var rfl)) (.var rfl) (.var rfl))))

theorem probe_typed {hole : Term} (typed : HasType [] hole (.arr (.ref .int) (.ref .int))) :
    HasType [] (probe hole) .bool :=
  .letE typed (.letE .refZero (.letE (.app (.var rfl) (.var rfl))
    (.ptrEq (.app (.var rfl) (.var rfl)) (.var rfl))))

theorem maker_returns_iff {which : Example} {s t : Store} {v : Value} :
    Eval [] (maker which) s v t ↔
      ∃ x y, x ∉ s ∧ y ∉ allocZero s x ∧
        v = .closure (functionBody which) [.address y, .address x] ∧ t = allocZero (allocZero s x) y := by
  simp only [maker, eval_let_iff, eval_refZero_iff, eval_lam_iff]
  constructor
  · rintro ⟨_, _, ⟨x, freshX, rfl, rfl⟩, _, _, ⟨y, freshY, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨x, y, freshX, freshY, rfl, rfl⟩
  · rintro ⟨x, y, freshX, freshY, rfl, rfl⟩
    exact ⟨_, _, ⟨x, freshX, rfl, rfl⟩, _, _, ⟨y, freshY, rfl, rfl⟩, rfl, rfl⟩

private theorem body_returns_iff {which : Example} {a x y : Loc} {s t : Store} {v : Value} :
    Eval [.address a, .address y, .address x] (functionBody which) s v t ↔
      v = .address (if a = testedAddress which x y then y else x) ∧ t = s := by
  cases which <;>
    simp [functionBody, testedAddress, eval_cond_iff, eval_ptrEq_iff, eval_var_iff] <;>
    split <;> simp_all [eval_var_iff, eq_comm]

private def reply (which : Example) (x y a : Loc) : Loc :=
  if a = testedAddress which x y then y else x

private theorem call_returns_iff {ρ : List Value} {i j : Nat} {which : Example}
    {x y a : Loc} {s t : Store} {v : Value}
    (fn : ρ[i]? = some (.closure (functionBody which) [.address y, .address x]))
    (arg : ρ[j]? = some (.address a)) :
    Eval ρ (.app (.var i) (.var j)) s v t ↔ v = .address (reply which x y a) ∧ t = s := by
  simp [eval_app_iff, eval_var_iff, fn, arg, body_returns_iff, reply]

private theorem comparison_returns_iff (which : Example) (x y a first : Loc)
    {s t : Store} {v : Value} :
    Eval [.address first, .address a, .closure (functionBody which) [.address y, .address x]]
      (.ptrEq (.app (.var 2) (.var 0)) (.var 0)) s v t ↔
      v = .bool (decide (reply which x y first = first)) ∧ t = s := by
  have call {w : Value} {u : Store} :
      Eval [.address first, .address a, .closure (functionBody which) [.address y, .address x]]
        (.app (.var 2) (.var 0)) s w u ↔ w = .address (reply which x y first) ∧ u = s :=
    call_returns_iff rfl rfl
  simp [eval_ptrEq_iff, call, eval_var_iff, and_comm]

private theorem two_calls_iff (which : Example) (x y a : Loc)
    {s t : Store} {v : Value} :
    Eval [.address a, .closure (functionBody which) [.address y, .address x]]
      (.letE (.app (.var 1) (.var 0)) (.ptrEq (.app (.var 2) (.var 0)) (.var 0))) s v t ↔
      v = .bool (decide (reply which x y (reply which x y a) = reply which x y a)) ∧ t = s := by
  rw [eval_let_iff]
  constructor
  · rintro ⟨first, intermediate, firstRun, comparison⟩
    obtain ⟨rfl, rfl⟩ := (call_returns_iff rfl rfl).mp firstRun
    exact (comparison_returns_iff which x y a _).mp comparison
  · intro result
    exact ⟨_, _, (call_returns_iff rfl rfl).mpr ⟨rfl, rfl⟩,
      (comparison_returns_iff which x y a _).mpr result⟩

/-- The first two addresses belong to the function and the third to the client. -/
def Fresh (s : Store) (x y a : Loc) : Prop :=
  x ∉ s ∧ y ∉ allocZero s x ∧ a ∉ allocZero (allocZero s x) y

def finalStore (s : Store) (x y a : Loc) : Store :=
  allocZero (allocZero (allocZero s x) y) a

theorem fresh_exists (s : Store) : ∃ x y a, Fresh s x y a :=
  ⟨s.freshAddress, _, _, s.freshAddress_not_mem,
    (allocZero s s.freshAddress).freshAddress_not_mem,
    (allocZero (allocZero s s.freshAddress) _).freshAddress_not_mem⟩

def observed : Example → Bool
  | .f => false
  | .g => true

private theorem replies_test {which : Example} {s : Store} {x y a : Loc} (fresh : Fresh s x y a) :
    decide (reply which x y (reply which x y a) = reply which x y a) = observed which := by
  obtain ⟨_, freshY, freshA⟩ := fresh
  have y_ne_x : y ≠ x := fun eq => freshY (Finmap.mem_insert.mpr (.inl eq))
  have a_ne_x : a ≠ x := fun eq => freshA
    (Finmap.mem_insert.mpr (.inr (Finmap.mem_insert.mpr (.inl eq))))
  have a_ne_y : a ≠ y := fun eq => freshA (Finmap.mem_insert.mpr (.inl eq))
  cases which <;> simp [reply, testedAddress, observed, a_ne_x, a_ne_y, y_ne_x, Ne.symm y_ne_x]

/-- Both directions quantify over the relational allocator. Every completed
probe has exactly this result and store, and every fresh triple realizes it. -/
theorem probe_returns_iff {which : Example} {s t : Store} {v : Value} :
    Eval [] (probe (maker which)) s v t ↔
      ∃ x y a, Fresh s x y a ∧ v = .bool (observed which) ∧ t = finalStore s x y a := by
  rw [probe, eval_let_iff]
  constructor
  · rintro ⟨_, _, makerRun, clientRun⟩
    obtain ⟨x, y, freshX, freshY, rfl, rfl⟩ := maker_returns_iff.mp makerRun
    obtain ⟨_, _, allocRun, callsRun⟩ := eval_let_iff.mp clientRun
    obtain ⟨a, freshA, rfl, rfl⟩ := eval_refZero_iff.mp allocRun
    have fresh : Fresh s x y a := ⟨freshX, freshY, freshA⟩
    have result := (two_calls_iff which x y a).mp callsRun
    rw [replies_test fresh] at result
    exact ⟨x, y, a, fresh, result.1, result.2⟩
  · rintro ⟨x, y, a, fresh, rfl, rfl⟩
    refine ⟨_, _, maker_returns_iff.mpr ⟨x, y, fresh.1, fresh.2.1, rfl, rfl⟩, ?_⟩
    apply eval_let_iff.mpr
    refine ⟨_, _, Eval.refZero fresh.2.2, (two_calls_iff which x y a).mpr ?_⟩
    rw [replies_test fresh]
    exact ⟨rfl, rfl⟩

def forever : L3.Expr := .loop (.bool true) .skip

/-- Turn the Boolean test into a closing unit context by looping on false. -/
def observe (hole : Term) : Term :=
  .cond (probe hole) (.coreUnit .skip) (.coreUnit forever)

theorem observe_typed {hole : Term} (typed : HasType [] hole (.arr (.ref .int) (.ref .int))) :
    HasType [] (observe hole) .unit :=
  .cond (probe_typed typed) (.coreUnit .skip) (.coreUnit (.loop (.bool true) .skip))

private def LoopState (s : Store) (c : L3.Config) : Prop :=
  c = ⟨forever, s⟩ ∨ c = ⟨.cond (.bool true) (.seq .skip forever) .skip, s⟩ ∨
    c = ⟨.seq .skip forever, s⟩

private theorem loop_step {s : Store} {before after : L3.Config}
    (inLoop : LoopState s before) (step : L3.Step before after) : LoopState s after := by
  rcases inLoop with rfl | rfl | rfl
  · change L3.Step ⟨.loop (.bool true) .skip, s⟩ after at step
    cases step
    exact .inr (.inl rfl)
  · cases step with
    | ifTrue => exact .inr (.inr rfl)
    | ifStep inner => cases inner
  · cases step with
    | seqSkip => exact .inl rfl
    | seqStep inner => cases inner

private theorem loop_no_return {s t : Store} (path : L3.Steps ⟨forever, s⟩ ⟨.skip, t⟩) : False := by
  have along {before after : L3.Config} (steps : L3.Steps before after)
      (start : LoopState s before) : LoopState s after := by
    induction steps with
    | refl => exact start
    | tail _ step ih => exact loop_step ih step
  rcases along path (.inl rfl) with eq | eq | eq <;> cases eq

private theorem skip_return_store {s t : Store} (path : L3.Steps ⟨.skip, s⟩ ⟨.skip, t⟩) : t = s := by
  rcases path.cases_head with eq | ⟨_, step, _⟩
  · cases eq
    rfl
  · cases step

theorem loop_diverges (s : Store) : InfiniteTrace L3.Step ⟨forever, s⟩ := by
  apply InfiniteTrace.coinduct (LoopState s) ?_ (.inl rfl)
  rintro _ (rfl | rfl | rfl)
  · exact ⟨_, .while, .inr (.inl rfl)⟩
  · exact ⟨_, .ifTrue, .inr (.inr rfl)⟩
  · exact ⟨_, .seqSkip, .inl rfl⟩

/-- This one typed context returns only with `g`. The result characterizes
all its finite returns, including the store for every allocation choice. -/
theorem observe_returns_iff {which : Example} {s t : Store} {v : Value} :
    Eval [] (observe (maker which)) s v t ↔ which = .g ∧ v = .unit ∧
      ∃ x y a, Fresh s x y a ∧ t = finalStore s x y a := by
  rw [observe, eval_cond_iff]
  constructor
  · rintro ⟨b, intermediate, testRun, branchRun⟩
    obtain ⟨x, y, a, fresh, answer, rfl⟩ := probe_returns_iff.mp testRun
    have same := Value.bool.inj answer
    subst b
    cases which with
    | f =>
      change Eval [] (.coreUnit forever) (finalStore s x y a) v t at branchRun
      exact (loop_no_return (eval_coreUnit_iff.mp branchRun).2).elim
    | g =>
      change Eval [] (.coreUnit .skip) (finalStore s x y a) v t at branchRun
      obtain ⟨rfl, path⟩ := eval_coreUnit_iff.mp branchRun
      exact ⟨rfl, rfl, x, y, a, fresh, skip_return_store path⟩
  · rintro ⟨rfl, rfl, x, y, a, fresh, rfl⟩
    exact ⟨true, _, probe_returns_iff.mpr ⟨x, y, a, fresh, rfl, rfl⟩, .coreUnit .refl⟩

/-- Every permitted choice with `f` selects the core loop, which has an
infinite trace in the exact store left by the probe. -/
theorem f_selects_loop {s : Store} {x y a : Loc} (fresh : Fresh s x y a) :
    Eval [] (probe (maker .f)) s (.bool false) (finalStore s x y a) ∧
      InfiniteTrace L3.Step ⟨forever, finalStore s x y a⟩ :=
  ⟨probe_returns_iff.mpr ⟨x, y, a, fresh, rfl, rfl⟩, loop_diverges _⟩

theorem separated (s : Store) :
    (∃ t, Eval [] (observe (maker .g)) s .unit t) ∧
      ¬ ∃ v t, Eval [] (observe (maker .f)) s v t := by
  obtain ⟨x, y, a, fresh⟩ := fresh_exists s
  refine ⟨⟨_, observe_returns_iff.mpr ⟨rfl, rfl, x, y, a, fresh, rfl⟩⟩, ?_⟩
  rintro ⟨_, _, run⟩
  cases (observe_returns_iff.mp run).1

example : Eval [] (probe (maker .f)) ∅ (.bool false) (finalStore ∅ 2 5 9) :=
  probe_returns_iff.mpr
    ⟨2, 5, 9, by simp [Fresh, allocZero, Finmap.mem_insert, Finmap.notMem_empty], rfl, rfl⟩

example : Eval [] (observe (maker .g)) ∅ .unit (finalStore ∅ 9 2 5) :=
  observe_returns_iff.mpr
    ⟨rfl, rfl, 9, 2, 5, by simp [Fresh, allocZero, Finmap.mem_insert, Finmap.notMem_empty], rfl⟩

end Silmaril.Courses.Cambridge.L3.PointerEquality
