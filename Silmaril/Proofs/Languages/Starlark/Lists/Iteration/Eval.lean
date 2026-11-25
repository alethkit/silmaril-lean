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

theorem unpackValue_eq_of_unpacks {s : State} {value : Value} {arity : Nat}
    {out : Outcome (List Value)} (ran : UnpacksValue s value arity out) :
    unpackValue arity value s = out := by
  cases ran with
  | items read size yields =>
    simp [unpackValue, read, size, (cursorCollects_iff_collect _ _).mp yields]
  | arity read mismatch => simp [unpackValue, read, mismatch]
  | nonIterable read => simp [unpackValue, read]
  | readError read other => simp [unpackValue, read, other]

theorem unpacksValue_unpackValue (s : State) (value : Value) (arity : Nat) :
    UnpacksValue s value arity (unpackValue arity value s) := by
  simp only [unpackValue]
  cases read : acquireIterator value s with
  | error error next =>
    by_cases nonIterable : error = .notIterable
    · subst error
      exact .nonIterable read
    · simpa only [nonIterable, ite_false] using UnpacksValue.readError (arity := arity) read nonIterable
  | ok pair next =>
    obtain ⟨guard, cursor⟩ := pair
    by_cases size : cursor.remaining = arity
    · simp only [size, ite_true]
      exact .items read size ((cursorCollects_iff_collect _ _).mpr rfl)
    · simp only [size]
      exact .arity read size

theorem unpackValue_failure_state {s final : State} {value : Value} {arity : Nat} {error : Error}
    (ran : UnpacksValue s value arity (.error error final)) : final = s := by
  have kept : finishState (acquireIterator value s) = s := by
    cases value with
    | list | tuple | dict =>
      simp only [acquireIterator, map_finishState, iterationSource]
      exact projectCell_finishState _ _ s
    | _ => rfl
  cases ran with
  | arity read _ | nonIterable read | readError read _ =>
    rw [read] at kept
    exact kept

theorem bindTarget_eq_of_binds {s : State} {value : Value} {target : LoopTarget} {out : Outcome Unit}
    (ran : BindsTarget s value target out) : bindTarget target value s = out := by
  induction ran using BindsTarget.rec
    (motive_2 := fun state targets values result _ => bindTargets targets values state = result) with
  | name => rw [bindTarget]
  | sequence unpacked _ ih =>
    rw [bindTarget, unpackValue_eq_of_unpacks unpacked]
    exact ih
  | unpackError unpacked => rw [bindTarget, unpackValue_eq_of_unpacks unpacked]; rfl
  | noTargets => rw [bindTargets]
  | noValues _ targets => cases targets <;> rw [bindTargets]
  | next _ _ head tail => rw [bindTargets, head]; exact tail
  | failed _ head => rw [bindTargets, head]; rfl

mutual
theorem bindsTarget_bindTarget (s : State) (value : Value) (target : LoopTarget) :
    BindsTarget s value target (bindTarget target value s) := by
  cases target with
  | name binding =>
    rw [bindTarget]
    exact .name s value binding
  | sequence children =>
    rw [bindTarget]
    have ran := unpacksValue_unpackValue s value children.length
    cases result : unpackValue children.length value s with
    | error error next => exact .unpackError (result ▸ ran)
    | ok values next =>
      exact .sequence (result ▸ ran) (bindsTargets_bindTargets next children values)
termination_by sizeOf target
decreasing_by simp_wf <;> omega

theorem bindsTargets_bindTargets (s : State) (targets : List LoopTarget) (values : List Value) :
    BindsTargets s targets values (bindTargets targets values s) := by
  cases targets with
  | nil =>
    rw [bindTargets]
    exact .noTargets s values
  | cons target rest =>
    cases values with
    | nil =>
      rw [bindTargets]
      exact .noValues s (target :: rest)
    | cons value values =>
      rw [bindTargets]
      have head := bindsTarget_bindTarget s value target
      cases result : bindTarget target value s with
      | error error next => exact .failed (result ▸ head)
      | ok assigned next =>
        cases assigned
        exact .next (result ▸ head) (bindsTargets_bindTargets next rest values)
termination_by sizeOf targets
decreasing_by all_goals (simp_wf <;> omega)
end

private theorem flat_targets_succeed {s final : State} {bindings : List Binding} {values : List Value}
    {error : Error} (ran : BindsTargets s (bindings.map LoopTarget.name) values (.error error final)) : False := by
  induction bindings generalizing s values with
  | nil => cases ran
  | cons binding rest ih =>
    simp only [List.map_cons] at ran
    cases ran with
    | next _ tail => exact ih tail
    | failed head => cases head

theorem bindsTarget_failure_state {s final : State} {value : Value} {bindings : List Binding}
    {error : Error} (ran : BindsTarget s value (.unpack bindings) (.error error final)) : final = s := by
  cases ran with
  | sequence _ child => exact False.elim (flat_targets_succeed child)
  | unpackError failed => exact unpackValue_failure_state failed

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
