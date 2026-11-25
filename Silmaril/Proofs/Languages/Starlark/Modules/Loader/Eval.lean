module

public import Silmaril.Languages.Starlark.Modules.Loader.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Loader

open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Modules (enter validateSource)
open Silmaril.Languages.Starlark.Modules.Loader

theorem denote_eq_of_runs {program : Program} {manifest : Manifest} {α : Type}
    {active : List ModuleId} {job : Job α} {s : Session} {out : Result α}
    (h : Runs program manifest active job s out) :
    denote program manifest active job s = out := by
  induction h <;>
    (try have evaluated := (exec_iff_denoteBody _ _ _ _ _).mp (by assumption)) <;>
    simp_all only [denote, resume, run, ite_true, ite_false, dite_true, dite_false]

theorem runs_denote (program : Program) (manifest : Manifest)
    (active : List ModuleId) {α : Type} (job : Job α) (s : Session) :
    Runs program manifest active job s (denote program manifest active job s) := by
  cases job with
  | «initialize» id =>
    rw [denote]
    by_cases seen : id ∈ active
    · simpa only [ite_eq_left seen] using Runs.cycle (program := program) (manifest := manifest) (s := s) seen
    · simp only [ite_eq_right seen]
      cases cached : s.cache.lookup id with
      | some published => exact .cached seen cached
      | none =>
        by_cases bound : id < manifest.size
        · simp only [dite_eq_left bound]
          cases valid : validateSource program manifest[id].source with
          | error error => exact .reject bound seen cached valid
          | ok checked =>
            cases checked
            exact .initialize bound seen cached valid
              (runs_denote program manifest (id :: active) (.commands id manifest[id].source.commands)
                { s with runtime := enter manifest[id].source s.runtime })
        · simpa only [dite_eq_right bound] using
            Runs.unknownModule (program := program) (s := s) seen cached bound
  | command requester command =>
    cases command with
    | exec code =>
      rw [denote]
      exact .exec ((exec_iff_denoteBody _ _ _ _ _).mpr rfl)
    | load label imports =>
      rw [denote]
      cases found : resolve manifest requester label with
      | none => exact .missingLabel found
      | some id =>
        have dep := runs_denote program manifest active (.initialize id) s
        cases result : denote program manifest active (.initialize id) s with
        | error error next =>
          simpa only [result, resume] using Runs.loadFailed (imports := imports) found (result ▸ dep)
        | ok published next =>
          simpa only [result, resume] using Runs.load (imports := imports) found (result ▸ dep)
  | commands requester steps =>
    cases steps with
    | nil =>
      rw [denote]
      exact .done
    | cons first rest =>
      rw [denote]
      have step := runs_denote program manifest active (.command requester first) s
      cases result : denote program manifest active (.command requester first) s with
      | error error next => exact .failed (result ▸ step)
      | ok checked next =>
        cases checked
        exact .step (result ▸ step) (runs_denote program manifest active (.commands requester rest) next)
termination_by ((pending manifest active).length, job.weight)
decreasing_by
  all_goals first
    | apply Prod.Lex.left; exact pending_length_lt manifest active _ (by assumption) (by assumption)
    | apply Prod.Lex.right; simp [Job.weight]

end Silmaril.Proofs.Languages.Starlark.Modules.Loader
