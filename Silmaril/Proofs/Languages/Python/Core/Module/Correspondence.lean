module

public import Silmaril.Languages.Python.Core.Module.Defs
public import Silmaril.Languages.Python.Core.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Module

open Silmaril.Languages.Python.Core.Module
open Semantics.Operational

theorem identity_scan_iff {ε : Type} (left : Singleton)
    (links : List (IdentityOperator × (Unit → Except ε Singleton))) (result : Except ε Bool) :
    Identity.scan left links = result ↔ Identity.Scans left links result := by
  constructor
  · intro evaluated
    subst result
    induction links generalizing left with
    | nil => exact .done left
    | cons link rest ih =>
      obtain ⟨operator, read⟩ := link
      cases found : read () with
      | error error => simpa [Identity.scan, Except.bind, found] using Identity.Scans.error found
      | ok right =>
        cases matched : operator.test left right with
        | false => simpa [Identity.scan, Except.bind, found, matched] using Identity.Scans.stop found matched
        | true => simpa [Identity.scan, Except.bind, found, matched] using Identity.Scans.next found matched (ih right)
  · intro evaluated
    induction evaluated <;> simp_all [Identity.scan, Except.bind]

private theorem operator_eq {op : Operator} {left right : Value} {result : Evaluated}
    (rule : op.Eval left right result) : op.eval left right = result := by
  cases rule with
  | arithmetic left right rule =>
    simp [Operator.eval, left, right, Languages.Python.Core.BinOp.eval_iff.mpr rule]
  | unsupportedLeft left => simp [Operator.eval, left]
  | unsupportedRight left right => simp [Operator.eval, left, right]
  | equal same => simp [Operator.eval, same]
  | notEqual same => simp [Operator.eval, same]

private theorem operator_rule (op : Operator) (left right : Value) : op.Eval left right (op.eval left right) := by
  cases op with
  | arithmetic op =>
    cases first : left.asInt? with
    | none => simpa [Operator.eval, first] using Operator.Eval.unsupportedLeft first
    | some a =>
      cases second : right.asInt? with
      | none => simpa [Operator.eval, first, second] using Operator.Eval.unsupportedRight first second
      | some b => simpa [Operator.eval, first, second] using
          Operator.Eval.arithmetic first second (Languages.Python.Core.BinOp.eval_iff.mp (rfl : op.eval a b = _))
  | equal => exact .equal rfl
  | notEqual => exact .notEqual rfl

variable {globals : Globals} {expression : Expr} {result : Evaluated}

private theorem evaluated_eq (rule : expression.Evals globals result) : expression.eval globals = result := by
  induction rule with
  | literal => simp [Expr.eval]
  | found found => simp [Expr.eval, found]
  | missing missing => simp [Expr.eval, missing]
  | leftError _ left => simp [Expr.eval, left, Except.bind]
  | rightError _ _ left right => simp [Expr.eval, left, right, Except.bind]
  | binary _ _ op left right => simp [Expr.eval, left, right, Except.bind, operator_eq op]
  | identityHeadError _ failed left =>
    simp [Expr.eval, left, failed, Except.bind]
  | @identityChain _ links _ _ _ _ found walked left =>
    have mapped := List.attach_map_val (l := links) (f := fun (link : IdentityOperator × Expr) =>
      (link.1, fun _ : Unit => Identity.project Value.singleton? .unsupportedIdentity (link.2.eval globals)))
    rw [Expr.eval, left, mapped]
    simp only [Identity.project, Except.bind, found] at walked ⊢
    rw [(identity_scan_iff _ _ _).mpr walked]

private theorem evaluated_rule (globals : Globals) (expression : Expr) :
    expression.Evals globals (expression.eval globals) := by
  cases expression with
  | «literal» value => simpa [Expr.eval] using Expr.Evals.literal (globals := globals) value
  | readGlobal name =>
    cases found : globals.lookup name with
    | none => simpa [Expr.eval, found] using Expr.Evals.missing found
    | some value => simpa [Expr.eval, found] using Expr.Evals.found found
  | binary op left right =>
    have ihLeft := evaluated_rule globals left
    have ihRight := evaluated_rule globals right
    cases lhs : left.eval globals with
    | error error =>
      simpa [Expr.eval, lhs, Except.bind] using
        (Expr.Evals.leftError (op := op) (right := right) (lhs ▸ ihLeft))
    | ok first =>
      cases rhs : right.eval globals with
      | error error =>
        simpa [Expr.eval, lhs, rhs, Except.bind] using
          (Expr.Evals.rightError (op := op) (lhs ▸ ihLeft) (rhs ▸ ihRight))
      | ok second =>
        simpa [Expr.eval, lhs, rhs, Except.bind] using
          (Expr.Evals.binary (lhs ▸ ihLeft) (rhs ▸ ihRight) (operator_rule op first second))
  | identityChain left links =>
    have ihLeft := evaluated_rule globals left
    cases lhs : left.eval globals with
    | error error =>
      simpa [Expr.eval, lhs, Identity.project, Except.bind] using
        (Expr.Evals.identityHeadError (links := links) (lhs ▸ ihLeft) (rfl :
          Identity.project Value.singleton? .unsupportedIdentity (.error error) = .error error))
    | ok value =>
      cases found : value.singleton? with
      | none =>
        have failed : Identity.project Value.singleton? Error.unsupportedIdentity (.ok value) =
            .error .unsupportedIdentity := by simp [Identity.project, Except.bind, found]
        simpa [Expr.eval, lhs, Identity.project, Except.bind, found] using
          Expr.Evals.identityHeadError (links := links) (lhs ▸ ihLeft) failed
      | some first =>
        let suppliers : List (IdentityOperator × (Unit → Except Error Singleton)) :=
          links.map fun link =>
            (link.1, fun _ => Identity.project Value.singleton? Error.unsupportedIdentity (link.2.eval globals))
        have walked := (identity_scan_iff first suppliers _).mp rfl
        have mapped := List.attach_map_val (l := links) (f := fun (link : IdentityOperator × Expr) =>
          (link.1, fun _ : Unit => Identity.project Value.singleton? .unsupportedIdentity (link.2.eval globals)))
        rw [Expr.eval, lhs, mapped]
        simpa [Identity.project, Except.bind, found, suppliers] using
          Expr.Evals.identityChain (lhs ▸ ihLeft) found walked
termination_by sizeOf expression

theorem eval_iff : expression.eval globals = result ↔ expression.Evals globals result :=
  ⟨fun equal => equal ▸ evaluated_rule globals expression, evaluated_eq⟩

variable {source target : State} {label : Option Label}

private theorem advance_of_step (step : Step source label target) : source.advance = some (label, target) := by
  cases step with
  | empty => rfl
  | assign value => simp [State.advance, evaluated_eq value]
  | assignError error => simp [State.advance, evaluated_eq error, State.complete]
  | assertTrue condition trueValue => simp [State.advance, evaluated_eq condition, trueValue]
  | assertFalse condition falseValue => simp [State.advance, evaluated_eq condition, falseValue, State.complete]
  | assertError error => simp [State.advance, evaluated_eq error, State.complete]

private theorem step_of_advance {transition : Transition}
    (selected : source.advance = some transition) : Step source transition.1 transition.2 := by
  cases source with
  | finished observation => simp [State.advance] at selected
  | running globals body =>
    cases body with
    | nil =>
      simp only [State.advance, Option.some.injEq] at selected
      subst transition
      exact .empty globals
    | cons statement rest =>
      cases statement with
      | assignGlobal name expression =>
        cases evaluated : expression.eval globals with
        | ok value =>
          simp only [State.advance, evaluated, Option.some.injEq] at selected
          subst transition
          exact .assign (eval_iff.mp evaluated)
        | error error =>
          simp only [State.advance, evaluated, Option.some.injEq] at selected
          subst transition
          exact .assignError (eval_iff.mp evaluated)
      | «assert» condition =>
        cases evaluated : condition.eval globals with
        | error error =>
          simp only [State.advance, evaluated, Option.some.injEq] at selected
          subst transition
          exact .assertError (eval_iff.mp evaluated)
        | ok value =>
          cases truth : value.truth with
          | false =>
            simp [State.advance, evaluated, truth] at selected
            subst transition
            exact .assertFalse (eval_iff.mp evaluated) truth
          | true =>
            simp [State.advance, evaluated, truth] at selected
            subst transition
            exact .assertTrue (eval_iff.mp evaluated) truth

theorem advance_iff : source.advance = some (label, target) ↔ Step source label target :=
  ⟨step_of_advance, advance_of_step⟩

private theorem stopped (source : State) (selected : source.advance = none) :
    ∃ observation, source = .finished observation := by
  cases source with
  | finished observation => exact ⟨observation, rfl⟩
  | running globals body =>
    cases body with
    | nil => simp [State.advance] at selected
    | cons statement rest => cases statement <;> simp [State.advance] at selected

theorem step_decreases (step : Step source label target) : target.budget < source.budget := by
  cases step <;> simp [State.budget]

theorem noDiverges (source : State) : ¬ semantics.toOpSem.Diverges source := by
  induction source using (measure State.budget).wf.induction with
  | h source ih =>
    intro infinite
    obtain ⟨target, ⟨_, edge⟩, tail⟩ := infinite.unfold
    exact ih target (step_decreases edge) tail

theorem run_path (fuel : Nat) (source : State) :
    labelled.Path source (runPrefix fuel source).1 (runPrefix fuel source).2 := by
  induction fuel generalizing source with
  | zero => exact .nil source
  | succ fuel ih =>
    cases selected : source.advance with
    | none => simpa [runPrefix, selected] using (Labelled.Path.nil (sem := labelled) source)
    | some edge =>
      obtain ⟨label, target⟩ := edge
      have stepped := step_of_advance selected
      cases label with
      | none =>
        simpa [runPrefix, selected] using
          ((.silent stepped (ih target)) : labelled.Path source (runPrefix fuel target).1 (runPrefix fuel target).2)
      | some action =>
        simpa [runPrefix, selected] using
          ((.visible stepped (ih target)) :
            labelled.Path source (action :: (runPrefix fuel target).1) (runPrefix fuel target).2)

theorem run_finishes (source : State) (fuel : Nat) (enough : source.budget ≤ fuel) :
    ∃ observation, (runPrefix fuel source).2 = .finished observation := by
  induction fuel generalizing source with
  | zero =>
    cases source with
    | running globals body => simp [State.budget] at enough
    | finished observation => exact ⟨observation, rfl⟩
  | succ fuel ih =>
    cases selected : source.advance with
    | none =>
      obtain ⟨observation, final⟩ := stopped source selected
      exact ⟨observation, by simpa [runPrefix, selected] using final⟩
    | some edge =>
      obtain ⟨action, target⟩ := edge
      have decreases : target.budget < source.budget := step_decreases (step_of_advance selected)
      obtain ⟨observation, final⟩ := ih target (by omega)
      exact ⟨observation, by simpa [runPrefix, selected] using final⟩

private theorem path_exact {source final : State} {log : List Label}
    (path : labelled.Path source log final) (terminal : final.advance = none)
    {fuel : Nat} (enough : source.budget ≤ fuel) : runPrefix fuel source = (log, final) := by
  induction path generalizing fuel with
  | nil state => cases fuel <;> simp [runPrefix, terminal]
  | silent step tail ih =>
    have decreases := step_decreases step
    cases fuel with
    | zero => omega
    | succ fuel => simp [runPrefix, advance_of_step step, ih terminal (fuel := fuel) (by omega)]
  | visible step tail ih =>
    have decreases := step_decreases step
    cases fuel with
    | zero => omega
    | succ fuel => simp [runPrefix, advance_of_step step, ih terminal (fuel := fuel) (by omega)]

theorem finishes_iff {entry : Entry} {log : List Label} {outcome : Outcome Observation} :
    labelled.Finishes entry.start log outcome ↔
      ∃ observation, entry.run = (log, .finished observation) ∧ outcome = .returned observation := by
  constructor
  · rintro ⟨final, steps, observed⟩
    cases final with
    | running globals body => exact False.elim observed
    | finished observation => exact ⟨observation, path_exact steps rfl (Nat.le_refl _), observed⟩
  · rintro ⟨observation, ran, rfl⟩
    have path := run_path entry.start.budget entry.start
    change labelled.Path entry.start entry.run.1 entry.run.2 at path
    rw [ran] at path
    exact ⟨.finished observation, path, rfl⟩

end Silmaril.Proofs.Languages.Python.Core.Module
