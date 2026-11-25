module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Trace

/-! # Simulation and collapse of one-block traces

Compare finite runs in both directions. For duplicate feedback, the outer
trace joins inner runs by flattening the two local labels.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

noncomputable def one (body : Val → Result) : Result → Result :=
  cfgRun 1 (fun _ => body)

theorem one_local (body : Val → Result) (v : Val) :
    one body (.jump 0 v) = one body (body v) :=
  cfgRun_local _ _ (by decide)

theorem one_out (body : Val → Result) (i : Nat) (v : Val) :
    one body (.jump (i + 1) v) = .jump i v := by
  unfold one
  rw [cfgRun_out _ _ (by omega), Nat.add_sub_cancel]

inductive Run (body : Val → Result) : Result → Result → Prop where
  | out (i : Nat) (v : Val) : Run body (.jump (i + 1) v) (.jump i v)
  | fault : Run body .fault .fault
  | div : Run body .diverges .diverges
  | localStep {v : Val} {r : Result} : Run body (body v) r → Run body (.jump 0 v) r

theorem Run.eval {body : Val → Result} {e r : Result} (h : Run body e r) :
    one body e = r := by
  induction h with
  | out i v => exact one_out body i v
  | fault => exact cfgRun_fault 1 _
  | div => exact cfgRun_diverges 1 _
  | localStep _ ih => exact (one_local _ _).trans ih

theorem Run.of_path {body : Val → Result} {e r : Result} {k : Nat}
    (h : path (fun (_ : Fin 1) => body) (enter 1 e) k = .inl r) :
    Run body e r := by
  induction k generalizing e with
  | zero =>
    cases e with
    | fault => cases h; exact .fault
    | diverges => cases h; exact .div
    | jump i v =>
      cases i with
      | zero => cases h
      | succ i =>
        have eq : enter 1 (.jump (i + 1) v) = .inl (.jump i v) := by
          simp [enter, Nat.not_lt_of_ge (show 1 ≤ i + 1 by omega)]
        change enter 1 (.jump (i + 1) v) = _ at h
        rw [eq] at h
        cases h
        exact .out i v
  | succ k ih =>
    cases e with
    | fault =>
      change path _ (.inl .fault) (k + 1) = _ at h
      rw [path_absorb] at h
      cases h
      exact .fault
    | diverges =>
      change path _ (.inl .diverges) (k + 1) = _ at h
      rw [path_absorb] at h
      cases h
      exact .div
    | jump i v =>
      cases i with
      | zero =>
        apply Run.localStep
        apply ih
        rw [Nat.add_comm k 1, path_add] at h
        exact h
      | succ i =>
        have eq : enter 1 (.jump (i + 1) v) = .inl (.jump i v) := by
          simp [enter, Nat.not_lt_of_ge (show 1 ≤ i + 1 by omega)]
        rw [eq, path_absorb] at h
        cases h
        exact .out i v

theorem Run.of_eval {body : Val → Result} {e r : Result}
    (hr : r ≠ .diverges) (h : one body e = r) : Run body e r := by
  classical
  change finish (fun (_ : Fin 1) => body) (enter 1 e) = _ at h
  by_cases hex : ∃ out, terminates (fun (_ : Fin 1) => body) (enter 1 e) out
  · obtain ⟨out, k, hk⟩ := hex
    rw [finish_of_terminal _ _ hk] at h
    cases h
    exact of_path hk
  · rw [finish, dite_eq_right hex] at h
    exact (hr h.symm).elim

theorem one_eq_of_runs {body body' : Val → Result} {e e' : Result}
    (h : ∀ r, r ≠ .diverges → (Run body e r ↔ Run body' e' r)) :
    one body e = one body' e' := by
  by_cases hl : one body e = .diverges
  · by_cases hr : one body' e' = .diverges
    · exact hl.trans hr.symm
    · exact False.elim (hr (((h _ hr).mpr (.of_eval hr rfl)).eval.symm.trans hl))
  · exact (((h _ hl).mp (.of_eval hl rfl)).eval).symm

def onState (f : Val → Val) : Result → Result
  | .jump 0 v => .jump 0 (f v)
  | r => r

theorem run_simulation {body body' : Val → Result} {f : Val → Val} {good : Val → Prop}
    (stable : ∀ v w, good v → body v = .jump 0 w → good w)
    (comm : ∀ v, good v → body' (f v) = onState f (body v))
    {e : Result} (he : ∀ v, e = .jump 0 v → good v) {r : Result} :
    Run body e r ↔ Run body' (onState f e) r := by
  constructor
  · intro h
    induction h with
    | out i v => exact .out i v
    | fault => exact .fault
    | div => exact .div
    | @localStep v out h ih =>
      apply Run.localStep
      rw [comm v (he v rfl)]
      exact ih (fun w hw => stable v w (he v rfl) hw)
  · generalize he' : onState f e = e'
    intro h
    induction h generalizing e with
    | out i v =>
      cases e with
      | jump j w =>
        cases j with
        | zero => cases he'
        | succ j => cases he'; exact .out i v
      | fault => cases he'
      | diverges => cases he'
    | fault =>
      cases e with
      | jump j w => cases j <;> cases he'
      | fault => exact .fault
      | diverges => cases he'
    | div =>
      cases e with
      | jump j w => cases j <;> cases he'
      | fault => cases he'
      | diverges => cases he'; exact .div
    | @localStep v out h ih =>
      cases e with
      | jump j w =>
        cases j with
        | zero =>
          cases he'
          apply Run.localStep
          exact ih (fun x hx => stable w x (he w rfl) hx) (comm w (he w rfl)).symm
        | succ j => cases he'
      | fault => cases he'
      | diverges => cases he'


def mergeFeedback : Result → Result := mapOut (fun i v => .jump i.pred v)

noncomputable def innerFeedback (body : Val → Result) (v : Val) : Result :=
  one body (.jump 0 v)

theorem run_inner_to_merged {body : Val → Result} {e x r : Result}
    (inner : Run body e x) (next : Run (mergeFeedback ∘ body) x r) :
    Run (mergeFeedback ∘ body) (mergeFeedback e) r := by
  induction inner with
  | out i v => exact next
  | fault => exact next
  | div => exact next
  | localStep _ ih => exact .localStep (ih next)

theorem run_nested_to_merged {body : Val → Result} {e r : Result}
    (h : Run (innerFeedback body) e r) (hr : r ≠ .diverges) :
    Run (mergeFeedback ∘ body) e r := by
  induction h with
  | out i v => exact .out i v
  | fault => exact .fault
  | div => exact .div
  | @localStep v out next ih =>
    have hi : innerFeedback body v ≠ .diverges := by
      intro eq
      have obs := next.eval
      rw [eq, show one (innerFeedback body) .diverges = .diverges from cfgRun_diverges 1 _] at obs
      exact hr obs.symm
    have hin : Run body (.jump 0 v) (innerFeedback body v) := .of_eval hi rfl
    exact run_inner_to_merged hin (ih hr)

theorem run_merged_to_nested {body : Val → Result} {e r : Result}
    (h : Run (mergeFeedback ∘ body) e r) :
    ∀ x, mergeFeedback x = e → Run (innerFeedback body) (one body x) r := by
  induction h with
  | out i v =>
    intro x eq
    cases x with
    | fault => cases eq
    | diverges => cases eq
    | jump j w =>
      cases j with
      | zero => cases eq
      | succ j =>
        change Result.jump j w = .jump (i + 1) v at eq
        cases eq
        rw [one_out]
        exact .out i v
  | fault =>
    intro x eq
    cases x with
    | jump j v => cases eq
    | diverges => cases eq
    | fault => rw [show one body .fault = .fault from cfgRun_fault 1 _]; exact .fault
  | div =>
    intro x eq
    cases x with
    | jump j v => cases eq
    | fault => cases eq
    | diverges =>
      cases eq
      rw [show one body .diverges = .diverges from cfgRun_diverges 1 _]
      exact .div
  | @localStep v out next ih =>
    intro x eq
    cases x with
    | fault => cases eq
    | diverges => cases eq
    | jump j w =>
      cases j with
      | zero =>
        cases eq
        rw [one_local]
        exact ih _ rfl
      | succ j =>
        change Result.jump j w = .jump 0 v at eq
        cases eq
        rw [one_out]
        apply Run.localStep
        unfold innerFeedback
        rw [one_local]
        exact ih _ rfl

theorem one_codiagonal (body : Val → Result) (e : Result) :
    one (innerFeedback body) e = one (mergeFeedback ∘ body) e := by
  apply one_eq_of_runs
  intro r hr
  constructor
  · exact fun h => run_nested_to_merged h hr
  · intro h
    cases h with
    | out i v => exact .out i v
    | fault => exact .fault
    | div => exact .div
    | @localStep v r next =>
      apply Run.localStep
      unfold innerFeedback
      rw [one_local]
      exact run_merged_to_nested next _ rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
