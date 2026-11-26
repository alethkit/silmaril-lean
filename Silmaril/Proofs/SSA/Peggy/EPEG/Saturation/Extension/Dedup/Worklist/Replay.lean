module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Search
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {zero : P [] .count} {source target : Output P params results l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

theorem check_iff {fuel : Nat} {report : Report} :
    check zero fuel source report = some target ↔
      replay zero source report.sites = some target ∧
        report.sites.length ≤ fuel ∧ checkStop zero fuel target report = true := by
  by_cases budget : report.sites.length ≤ fuel
  · unfold check
    rw [ite_eq_left budget]
    simp only [budget, true_and]
    cases replay zero source report.sites with
    | none => simp
    | some reached =>
      by_cases ok : checkStop zero fuel reached report = true
      · simp only [ite_eq_left ok, Option.some.injEq]
        exact ⟨fun h => ⟨h, h ▸ ok⟩, And.left⟩
      · simp only [ite_eq_right ok, reduceCtorEq, Option.some.injEq, false_iff]
        rintro ⟨rfl, bad⟩
        exact ok bad
  · simp [check, budget]

theorem replay_eq_close {sites : List Nat} (hit : replay zero source sites = some target) :
    close zero source sites = target := by
  induction sites generalizing source with
  | nil => exact Option.some.inj hit
  | cons i rest ih =>
    unfold replay at hit
    split at hit
    · exact ih hit
    · cases hit

theorem replay_prefix {sites : List Nat} (hit : replay zero source sites = some target) (length : Nat) :
    replay zero source (sites.take length) = some (close zero source (sites.take length)) := by
  induction length generalizing source sites with
  | zero => rfl
  | succ length ih =>
    cases sites with
    | nil => rfl
    | cons address rest =>
      unfold replay at hit
      split at hit
      · rename_i enabled
        simpa only [List.take_succ_cons, replay, ite_eq_left enabled, close, List.foldl_cons] using ih hit
      · cases hit

theorem closed_iff (s : Output P params results l) : checkFixed zero s = true ↔ Fixed zero s := by
  simpa only [checkFixed, Option.isNone_iff_eq_none] using (next_none_iff (zero := zero) s)

theorem check_fixed {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target)
    (stop : report.stop = .fixed) : Fixed zero target := by
  have accepted := (check_iff.mp hit).2.2
  unfold checkStop at accepted
  rw [stop] at accepted
  exact (closed_iff target).mp accepted

theorem check_exhausted {fuel : Nat} {report : Report}
    (hit : check zero fuel source report = some target) (stop : report.stop = .exhausted) :
    report.sites.length = fuel ∧ ¬ Fixed zero target := by
  have accepted := (check_iff.mp hit).2.2
  unfold checkStop at accepted
  rw [stop] at accepted
  rcases Bool.and_eq_true_iff.mp accepted with ⟨budget, notClosed⟩
  exact ⟨of_decide_eq_true budget, fun closed => by
    rw [(closed_iff target).mpr closed] at notClosed
    cases notClosed⟩

private theorem checkStop_cons (fuel : Nat) (state : Output P params results l)
    (address : Nat) (report : Report) :
    checkStop zero (fuel + 1) state ⟨address :: report.sites, report.stop⟩ =
      checkStop zero fuel state report := by
  obtain ⟨sites, stop⟩ := report
  cases stop <;> simp [checkStop]

theorem run_checked (fuel : Nat) (s : Output P params results l) :
    check zero fuel s (run zero fuel s).report = some (run zero fuel s).state := by
  induction fuel generalizing s with
  | zero =>
    rw [run]
    cases pick : next zero s <;> simp [pick, check, replay, checkStop, checkFixed]
  | succ fuel ih =>
    rw [run]
    cases pick : next zero s with
    | none => simp [pick, check, replay, checkStop, checkFixed]
    | some i =>
      have enabled := next_enabled s i pick
      let rest := run zero fuel (visit zero s i.val)
      have accepted : check zero fuel (visit zero s i.val) rest.report = some rest.state :=
        ih (visit zero s i.val)
      obtain ⟨trace, budget, verified⟩ := check_iff.mp accepted
      change check zero (fuel + 1) s ⟨i.val :: rest.report.sites, rest.report.stop⟩ = some rest.state
      apply check_iff.mpr
      refine ⟨?_, Nat.succ_le_succ budget, (checkStop_cons fuel rest.state i.val rest.report).trans verified⟩
      simpa only [replay, ite_eq_left enabled] using trace

private theorem visit_reachable (sites : List Nat) (s : Output P params results l) :
    Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Reachable (Visits zero) s (close zero s sites) := by
  induction sites generalizing s with
  | nil => exact .refl
  | cons address rest ih =>
    exact Relation.ReflTransGen.head ⟨address, rfl⟩ (ih (visit zero s address))

theorem check_normal {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target)
    (stop : report.stop = .fixed) : Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.StableNormalForm Comparable (Visits zero) source target := by
  constructor
  · rw [← replay_eq_close (check_iff.mp hit).1]
    exact visit_reachable report.sites source
  · rintro other ⟨address, rfl⟩
    rw [fixed_visit target address (check_fixed hit stop)]
    exact Comparable.refl target

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
