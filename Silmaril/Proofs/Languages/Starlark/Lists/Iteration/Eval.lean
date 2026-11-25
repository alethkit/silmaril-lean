module

public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Iteration

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

theorem cursor_eq_of_runs {body : State → Outcome Flow → Prop} {meaning : Meaning Flow}
    {target : Binding} {cursor : Cursor} {state : State} {out : Outcome Flow}
    (bodyEq : ∀ s result, body s result → meaning s = result)
    (ran : CursorRuns body target cursor state out) :
    denoteCursor target meaning cursor state = out := by
  induction ran with
  | done exhausted => rw [denoteCursor, exhausted]
  | advance step ran next _ ih =>
    rw [denoteCursor, step]
    dsimp only
    rcases next with rfl | rfl <;> rw [bodyEq _ _ ran] <;> exact ih
  | breakLoop step ran => rw [denoteCursor, step]; dsimp only; rw [bodyEq _ _ ran]
  | returned step ran => rw [denoteCursor, step]; dsimp only; rw [bodyEq _ _ ran]
  | failed step ran => rw [denoteCursor, step]; dsimp only; rw [bodyEq _ _ ran]

theorem cursor_runs_denote (body : State → Outcome Flow → Prop) (meaning : Meaning Flow)
    (bodyRuns : ∀ s, body s (meaning s)) (target : Binding) (cursor : Cursor) (state : State) :
    CursorRuns body target cursor state (denoteCursor target meaning cursor state) := by
  rw [denoteCursor]
  cases step : cursor.advance with
  | none => exact .done step
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    have ran := bodyRuns (state.write target value)
    cases invoked : meaning (state.write target value) with
    | error error next => exact .failed step (invoked ▸ ran)
    | ok flow next =>
      cases flow with
      | breakLoop => exact .breakLoop step (invoked ▸ ran)
      | returned result => exact .returned step (invoked ▸ ran)
      | next =>
        exact .advance step (invoked ▸ ran) (Or.inl rfl)
          (cursor_runs_denote body meaning bodyRuns target rest next)
      | continueLoop =>
        exact .advance step (invoked ▸ ran) (Or.inr rfl)
          (cursor_runs_denote body meaning bodyRuns target rest next)
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
