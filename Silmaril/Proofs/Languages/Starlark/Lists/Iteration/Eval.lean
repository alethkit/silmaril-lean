module

public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Thms
import Silmaril.Proofs.Languages.Starlark.Lists.Iteration.Truth

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Iteration

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

private theorem collect_go_eq {cursor : Cursor} {values : List Value}
    (yields : CursorCollects cursor values) (reversed : List Value) :
    Cursor.collect.go cursor reversed = reversed.reverse ++ values := by
  induction yields generalizing reversed with
  | done exhausted => rw [Cursor.collect.go, exhausted, List.append_nil]
  | next step _ ih =>
    rw [Cursor.collect.go, step]
    simpa [List.reverse_cons, List.append_assoc] using ih (_ :: reversed)

private theorem collects (cursor : Cursor) : ∃ values, CursorCollects cursor values := by
  cases step : cursor.advance with
  | none => exact ⟨[], .done step⟩
  | some item =>
    obtain ⟨value, rest⟩ := item
    obtain ⟨tail, yields⟩ := collects rest
    exact ⟨value :: tail, .next step yields⟩
termination_by cursor.remaining
decreasing_by exact Cursor.advance_decreases step

theorem cursorCollects_iff_collect (cursor : Cursor) (values : List Value) :
    CursorCollects cursor values ↔ cursor.collect = values := by
  have eq {items : List Value} (yields : CursorCollects cursor items) : cursor.collect = items :=
    collect_go_eq yields []
  refine ⟨eq, fun equal => ?_⟩
  obtain ⟨items, yields⟩ := collects cursor
  exact ((eq yields).symm.trans equal) ▸ yields

theorem cursorCollects_length {cursor : Cursor} {values : List Value}
    (ran : CursorCollects cursor values) : values.length = cursor.remaining := by
  induction ran with
  | @done finished empty =>
    cases finished with
    | items values => cases values <;> simp [Cursor.advance, Cursor.remaining] at empty ⊢
    | range current stride count => cases count <;> simp [Cursor.advance, Cursor.remaining] at empty ⊢
  | next step _ ih => exact (congrArg (· + 1) ih).trans (Cursor.advance_remaining step)

private theorem writes_eq {s final : State} {assignments : List (Binding × Value)}
    (ran : WritesBindings s assignments final) : writeBindings s assignments = final := by
  induction ran with
  | done => rfl
  | next _ ih => exact ih

private theorem writes (s : State) (assignments : List (Binding × Value)) :
    WritesBindings s assignments (writeBindings s assignments) := by
  induction assignments generalizing s with
  | nil => exact .done s
  | cons assignment rest ih =>
    obtain ⟨binding, value⟩ := assignment
    exact .next (ih (s.write binding value))

theorem bindTarget_eq_of_binds {s : State} {value : Value} {target : LoopTarget} {out : Outcome Unit}
    (ran : BindsTarget s value target out) : bindTarget target value s = out := by
  cases ran with
  | name => rfl
  | unpack read arity yields assigned =>
    simp [bindTarget, read, arity, (cursorCollects_iff_collect _ _).mp yields, writes_eq assigned]
  | arity read mismatch => simp [bindTarget, read, mismatch]
  | nonIterable _ read => simp [bindTarget, read]
  | readError _ read other => simp [bindTarget, read, other]

theorem bindsTarget_bindTarget (s : State) (value : Value) (target : LoopTarget) :
    BindsTarget s value target (bindTarget target value s) := by
  cases target with
  | name binding => exact .name binding
  | unpack bindings =>
    simp only [bindTarget]
    cases read : acquireIterator value s with
    | error error next =>
      by_cases nonIterable : error = .notIterable
      · subst error
        exact .nonIterable bindings read
      · simpa only [nonIterable, ite_false] using BindsTarget.readError bindings read nonIterable
    | ok pair next =>
      obtain ⟨guard, cursor⟩ := pair
      by_cases arity : cursor.remaining = bindings.length
      · simp only [arity, ite_true]
        exact .unpack read arity ((cursorCollects_iff_collect _ _).mpr rfl) (writes next _)
      · simp only [arity]
        exact .arity read arity

theorem bindsTarget_failure_state {s final : State} {value : Value} {target : LoopTarget}
    {error : Error} (ran : BindsTarget s value target (.error error final)) : final = s := by
  have kept : finishState (acquireIterator value s) = s := by
    cases value with
    | list | tuple | dict =>
      simp only [acquireIterator, map_finishState, iterationSource]
      exact projectCell_finishState _ _ s
    | _ => rfl
  cases ran with
  | arity read _ | nonIterable _ read | readError _ read _ =>
    rw [read] at kept
    exact kept

theorem cursor_eq_of_runs {body : State → Outcome Flow → Prop} {meaning : Meaning Flow}
    {target : LoopTarget} {cursor : Cursor} {state : State} {out : Outcome Flow}
    (bodyEq : ∀ s result, body s result → meaning s = result)
    (ran : CursorRuns body target cursor state out) :
    denoteCursor target meaning cursor state = out := by
  induction ran with
  | done exhausted => rw [denoteCursor, exhausted]
  | advance step bound ran next _ ih =>
    rw [denoteCursor, step]
    dsimp only
    rw [bindTarget_eq_of_binds bound]
    simp only [Outcome.resume]
    rcases next with rfl | rfl <;> rw [bodyEq _ _ ran] <;> exact ih
  | breakLoop step bound ran | returned step bound ran | failed step bound ran =>
    rw [denoteCursor, step]
    dsimp only
    simp only [bindTarget_eq_of_binds bound, Outcome.resume, bodyEq _ _ ran]
  | bindingError step bound =>
    rw [denoteCursor, step]
    dsimp only
    rw [bindTarget_eq_of_binds bound]
    rfl

theorem cursor_runs_denote (body : State → Outcome Flow → Prop) (meaning : Meaning Flow)
    (bodyRuns : ∀ s, body s (meaning s)) (target : LoopTarget) (cursor : Cursor) (state : State) :
    CursorRuns body target cursor state (denoteCursor target meaning cursor state) := by
  rw [denoteCursor]
  cases step : cursor.advance with
  | none => exact .done step
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    have bound := bindsTarget_bindTarget state value target
    cases binding : bindTarget target value state with
    | error error next => exact .bindingError step (binding ▸ bound)
    | ok boundValue next =>
      cases boundValue
      simp only [Outcome.resume]
      have ran := bodyRuns next
      have assigned := binding ▸ bound
      cases invoked : meaning next with
      | error error final => exact .failed step assigned (invoked ▸ ran)
      | ok flow final =>
        cases flow with
        | breakLoop => exact .breakLoop step assigned (invoked ▸ ran)
        | returned result => exact .returned step assigned (invoked ▸ ran)
        | next =>
          exact .advance step assigned (invoked ▸ ran) (Or.inl rfl)
            (cursor_runs_denote body meaning bodyRuns target rest final)
        | continueLoop =>
          exact .advance step assigned (invoked ▸ ran) (Or.inr rfl)
            (cursor_runs_denote body meaning bodyRuns target rest final)
termination_by cursor.remaining
decreasing_by all_goals exact Cursor.advance_decreases step

private def meaning : Work → Meaning Flow
  | .suite code => denoteSuite code
  | .cursor target body remaining => denoteCursor target (denoteSuite body) remaining

private theorem branch_apply {depth : Nat} (flag : Bool) (yes no : Suite depth) (state : State) :
    (if flag then denoteSuite yes else denoteSuite no) state =
      denoteSuite (if flag then yes else no) state := by
  cases flag <;> rfl

private theorem meaning_of_runs {s : State} {job : Work} {out : Outcome Flow}
    (h : Runs s job out) : meaning job s = out := by
  induction h
  case cursor _ ran ih => exact cursor_eq_of_runs ih ran
  all_goals
    (try have evaluated := (eval_iff_denote _ _ _).mp (by assumption)) <;>
      simp_all [meaning, denoteSuite, denoteForIn, Outcome.resume, branch_apply]
  case seqStop signal _ _ _ =>
    cases signal <;> simp_all <;> rfl

theorem denoteSuite_eq_of_runs {depth : Nat} {s : State} {code : Suite depth} {out : Outcome Flow}
    (h : Runs s (.suite code) out) : denoteSuite code s = out :=
  meaning_of_runs h

theorem runs_denoteSuite {depth : Nat} (code : Suite depth) (state : State) :
    Runs state (.suite code) (denoteSuite code state) := by
  induction code generalizing state with
  | atomic stmt => exact .atomic ((eval_iff_denote _ _ _).mpr rfl)
  | seq first rest ihFirst ihRest =>
    rw [denoteSuite]
    cases h : denoteSuite first state with
    | error error next =>
      exact .seqError (h ▸ ihFirst state)
    | ok flow next =>
      cases flow with
      | next => exact .seq (h ▸ ihFirst state) (ihRest next)
      | breakLoop => exact .seqStop (h ▸ ihFirst state) (by intro equality; cases equality)
      | continueLoop => exact .seqStop (h ▸ ihFirst state) (by intro equality; cases equality)
      | returned result => exact .seqStop (h ▸ ihFirst state) (by intro equality; cases equality)
  | branch test yes no ihYes ihNo =>
    rw [denoteSuite]
    have tested : Eval state test (denote test state) := (eval_iff_denote _ _ _).mpr rfl
    cases h : Outcome.resume (denote test state) truth with
    | error error next => exact .branchError tested h
    | ok flag next =>
      cases flag
      · exact .branch tested h (ihNo next)
      · exact .branch tested h (ihYes next)
  | forIn target iterable body ihBody =>
    rw [denoteSuite, denoteForIn]
    have evaluated : Eval state iterable (denote iterable state) := (eval_iff_denote _ _ _).mpr rfl
    cases h : Outcome.resume (denote iterable state) acquireIterator with
    | error error next => exact .forError evaluated h
    | ok source next =>
      obtain ⟨guard, cursor⟩ := source
      let bodyRuns : State → Outcome Flow → Prop := fun s out => denoteSuite body s = out
      exact .forIn evaluated h (.cursor (bodyRuns := bodyRuns) (fun s _ eq => eq ▸ ihBody s)
        (cursor_runs_denote bodyRuns (denoteSuite body) (fun _ => rfl) target cursor (enterIterator next guard)))
  | breakLoop => exact .breakLoop
  | continueLoop => exact .continueLoop
  | ret value => exact .ret ((eval_iff_denote _ _ _).mpr rfl)

end Silmaril.Proofs.Languages.Starlark.Lists.Iteration
