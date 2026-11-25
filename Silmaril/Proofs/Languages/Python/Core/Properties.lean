module

public import Silmaril.Proofs.Languages.Python.Core.Execution
public import Silmaril.Semantics.Operational.Program.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core

open Silmaril.Languages.Python.Core Silmaril.Semantics.Operational

variable {profile : Profile} {source target : State} {label : Option Completion}
  {body : Body} {outcome : Outcome Completion} {fuel : Nat}

private theorem expr_preserves {expr : Expr} {next : Except Exception Expr}
    (step : expr.Step next) (supported : profile.supports expr) :
    (State.resume next).supported profile := by
  induction step with
  | @left op left right next step ih =>
    simp only [Profile.supports, Bool.and_eq_true] at supported
    have child := ih supported.1.2
    cases next <;>
      simp_all [Except.map, State.resume, State.supported, Profile.supports]
  | @right op left right next step ih =>
    simp only [Profile.supports, Bool.and_eq_true] at supported
    have child := ih supported.2
    cases next <;>
      simp_all [Except.map, State.resume, State.supported, Profile.supports]
  | compute eval =>
    cases eval <;> rfl

theorem step_preserves (step : Step source label target) (supported : source.supported profile) :
    target.supported profile := by
  cases step with
  | expr step => exact expr_preserves step supported
  | ret | raise => rfl

private theorem expr_work {expr : Expr} {next : Except Exception Expr} (step : expr.Step next) :
    match next with
    | .ok target => target.work < expr.work
    | .error _ => True := by
  induction step with
  | @left op left right next step ih =>
    cases next <;> simp [Except.map, Expr.work] at ih ⊢
    omega
  | @right op left right next step ih =>
    cases next <;> simp [Except.map, Expr.work] at ih ⊢
    omega
  | compute eval => cases eval <;> simp [Except.map, Expr.work]

theorem step_decreases (step : Step source label target) : target.budget < source.budget := by
  cases step with
  | @expr expr next step =>
    have work := expr_work step
    cases next <;> simp [State.resume, State.budget] at work ⊢
    omega
  | ret => simp [State.budget, Expr.work]
  | raise => simp [State.budget]

private theorem expr_result {expr : Expr} {next : Except Exception Expr} (step : expr.Step next) :
    expr.eval = next.bind Expr.eval := by
  induction step with
  | @left op left right next step ih =>
    cases next <;> simp [Except.map, Expr.eval, Except.bind, ih]
  | @right op left right next step ih =>
    cases next <;> simp [Except.map, Expr.eval, Except.bind, ih]
  | compute eval => cases eval <;> simp_all [Expr.eval, Except.map, Except.bind, BinOp.eval]

theorem step_result (step : Step source label target) : source.result = target.result := by
  cases step with
  | @expr expr next step =>
    have result := expr_result step
    cases next <;> exact result
  | ret | raise => rfl

private theorem reach_supported (supported : source.supported profile)
    (reach : (semantics profile).toOpSem.Reach source target) : target.supported profile := by
  induction reach with
  | refl => exact supported
  | tail _ step ih =>
    obtain ⟨_, _, edge⟩ := step
    exact step_preserves edge ih

theorem safe (supported : source.supported profile) : (semantics profile).SafeAt source := by
  rintro ⟨target, reach, marked⟩
  rcases marked with impossible | denied
  · exact impossible
  · exact denied (reach_supported supported reach)

theorem noDiverges (profile : Profile) (source : State) :
    ¬ (semantics profile).toOpSem.Diverges source := by
  induction source using (measure State.budget).wf.induction with
  | h source ih =>
    intro infinite
    obtain ⟨target, ⟨_, _, edge⟩, tail⟩ := infinite.unfold
    exact ih target (step_decreases edge) tail

theorem finishes_in_budget (supported : source.supported profile) :
    ∃ length, length ≤ source.budget ∧
      StepsN (semantics profile).step length source (.finished source.result) := by
  induction source using (measure State.budget).wf.induction with
  | h source ih =>
    rcases progress supported with ⟨label, target, edge⟩ | ⟨_, observed⟩
    · have decreases := step_decreases edge.2
      obtain ⟨length, bound, tail⟩ := ih target decreases (step_preserves edge.2 supported)
      rw [step_result edge.2]
      exact ⟨length + 1, by omega, .cons ⟨supported, label, edge.2⟩ tail⟩
    · cases observed
      exact ⟨0, Nat.zero_le _, .nil _⟩

private theorem reach_result (reach : (semantics profile).toOpSem.Reach source target) :
    source.result = target.result := by
  induction reach with
  | refl => rfl
  | tail _ step ih =>
    obtain ⟨_, _, edge⟩ := step
    exact ih.trans (step_result edge)

theorem may_iff (supported : source.supported profile) :
    (semantics profile).toOpSem.May source outcome ↔ outcome = .returned source.result := by
  constructor
  · rintro ⟨target, reach, _, observed⟩
    cases observed
    exact congrArg Outcome.returned (reach_result reach).symm
  · rintro rfl
    obtain ⟨_, _, path⟩ := finishes_in_budget supported
    exact ⟨_, path.reach, rfl, .finished _⟩

theorem start_iff : body.start? profile = some source ↔ (model profile).initial body source := by
  by_cases supported : profile.supports body.value
  · simp only [Body.start?, model, supported, ite_true, Option.some.injEq, true_and]
    exact eq_comm
  · simp [Body.start?, model, supported]

theorem noEntry_iff : (model profile).NoEntry body ↔ ¬ profile.supports body.value :=
  ⟨fun missing supported => missing ⟨body.start, supported, rfl⟩, fun unsupported ⟨_, supported, _⟩ => unsupported supported⟩

theorem model_may_iff :
    (model profile).May body outcome ↔ profile.supports body.value ∧ outcome = .returned body.value.eval := by
  constructor
  · rintro ⟨source, ⟨supported, rfl⟩, may⟩
    exact ⟨supported, (may_iff (source := body.start) (profile := profile) supported).mp may⟩
  · rintro ⟨supported, rfl⟩
    exact ⟨body.start, ⟨supported, rfl⟩, (may_iff (source := body.start) (profile := profile) supported).mpr rfl⟩

theorem model_safe : ¬ (model profile).UBReachable body :=
  fun ⟨_, ⟨supported, rfl⟩, bad⟩ => safe (source := body.start) (profile := profile) supported bad

theorem run_exact (oracle : Oracle (semantics profile))
    (known : ∀ state, oracle.pick state ≠ .stop .unknown)
    (supported : source.supported profile) (enough : source.budget ≤ fuel) :
    oracle.run source fuel =
      .stop (.finished source.result) (.observed (.returned source.result)) := by
  obtain ⟨_, bound, path⟩ := finishes_in_budget supported
  exact Oracle.run_complete _ path ⟨rfl, .finished _⟩ (bound.trans enough)
    (detFrom profile source) (terminal profile) (safe supported) (fun {s} _ => known s)


private theorem path_of_steps {length : Nat} (path : StepsN (semantics profile).step length source target) :
    ∃ log, (labelled profile).Path source log target := by
  induction path with
  | nil state => exact ⟨[], .nil state⟩
  | cons step _ ih =>
    obtain ⟨supported, label, edge⟩ := step
    obtain ⟨log, path⟩ := ih
    cases label with
    | none => exact ⟨log, .silent ⟨supported, edge⟩ path⟩
    | some event => exact ⟨event :: log, .visible ⟨supported, edge⟩ path⟩

private theorem path_reach {log : List Completion} (path : (labelled profile).Path source log target) :
    (semantics profile).toOpSem.Reach source target := by
  induction path with
  | nil => exact .refl
  | silent step _ ih => exact .head ⟨step.1, none, step.2⟩ ih
  | @visible _ _ _ _ event step _ ih => exact .head ⟨step.1, some event, step.2⟩ ih

private def remainingLog : State → List Completion
  | .finished _ => []
  | state => [state.result]

private theorem finished_log {result : Completion} {log : List Completion}
    (path : (labelled profile).Path (.finished result) log target) : log = [] := by
  cases path with
  | nil => rfl
  | silent edge _ => cases edge.2
  | visible edge _ => cases edge.2

private theorem path_log {log : List Completion} (path : (labelled profile).Path source log target)
    (observed : Observes target outcome) : log = remainingLog source := by
  induction path with
  | nil =>
    cases observed
    rfl
  | silent edge _ ih =>
    have result := step_result edge.2
    cases edge.2 with
    | @expr expr next step =>
      cases next <;> exact ih observed |>.trans (congrArg (fun r => [r]) result.symm)
  | visible edge tail _ =>
    cases edge.2 <;> rw [finished_log tail] <;> rfl

theorem labelled_finishes_iff {log : List Completion} (supported : profile.supports body.value) :
    (labelled profile).Finishes body.start log outcome ↔
      log = [body.value.eval] ∧ outcome = .returned body.value.eval := by
  constructor
  · rintro ⟨target, path, observed⟩
    exact ⟨path_log path observed.2, (may_iff (source := body.start) (profile := profile) supported).mp ⟨target, path_reach path, observed⟩⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨_, _, path⟩ := finishes_in_budget (source := body.start) supported
    obtain ⟨log, labelledPath⟩ := path_of_steps path
    have observed : Observes (.finished body.value.eval) (.returned body.value.eval) := .finished _
    have eq : log = [body.value.eval] := path_log labelledPath observed
    exact ⟨_, eq ▸ labelledPath, rfl, observed⟩

end Silmaril.Proofs.Languages.Python.Core
