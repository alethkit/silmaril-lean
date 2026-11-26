module

public import Silmaril.SSA.Peggy.Optimizer.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.Optimizer

open Silmaril.SSA
open Silmaril.SSA.Peggy.Optimizer
open Silmaril.SSA.Peggy.Bridge.Egg
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {out : PEG.Ty Data}
variable {p : Program P params out} {r : Rule P out} {rs : List (Rule P out)}

theorem match_sound {source : RankedProgram P params results} {target : Term P params out}
    (found : TermMatch source r target) (M : Core.Model (signature P))
    (env : ∀ i, M.carrier (context params i)) (law : r.core.Holds M)
    (guards : ∀ e ∈ r.guards,
      (Core.Pattern.instantiate (termSub found.binding) e.lhs).eval M env =
        (Core.Pattern.instantiate (termSub found.binding) e.rhs).eval M env) :
    target.eval M env =
      (Core.Pattern.instantiate (termSub found.binding) r.rhs.term).eval M env := by
  let δ := termSub found.binding
  have guardValues : ∀ e ∈ r.core.guards, e.Holds M (fun i => (δ i).eval M env) := by
    intro e mem
    unfold Core.Equality.Holds
    rw [← Core.Pattern.eval_instantiate δ M env, ← Core.Pattern.eval_instantiate δ M env]
    exact guards e mem
  have conclusion := law (fun i => (δ i).eval M env) guardValues
  calc
    _ = (Core.Pattern.instantiate δ r.lhs).eval M env :=
      congrArg (fun t : Term P params out => t.eval M env) found.fits.symm
    _ = r.lhs.eval M (fun i => (δ i).eval M env) := Core.Pattern.eval_instantiate δ M env _
    _ = r.rhs.term.eval M (fun i => (δ i).eval M env) := conclusion
    _ = _ := (Core.Pattern.eval_instantiate δ M env r.rhs.term).symm

variable {rules : List (Core.Rule (signature P))} {source : RankedProgram P params results}
variable (cost : RankedProgram P params results → Nat)

private theorem prefer_left (left right : CheckedProgram rules source) :
    cost (CheckedProgram.preferBy cost left right).program ≤ cost left.program := by
  unfold CheckedProgram.preferBy
  split
  next h => exact Nat.le_of_lt h
  next => exact Nat.le_refl _

private theorem prefer_right (left right : CheckedProgram rules source) :
    cost (CheckedProgram.preferBy cost left right).program ≤ cost right.program := by
  unfold CheckedProgram.preferBy
  split
  next => exact Nat.le_refl _
  next h => exact Nat.le_of_not_gt h

private theorem fold_le_seed (options : List (CheckedProgram rules source)) (seed : CheckedProgram rules source) :
    cost (options.foldl (CheckedProgram.preferBy cost) seed).program ≤ cost seed.program := by
  induction options generalizing seed with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact (ih (CheckedProgram.preferBy cost seed head)).trans (prefer_left cost seed head)

theorem fold_le_member (options : List (CheckedProgram rules source)) (seed : CheckedProgram rules source)
    {candidate : CheckedProgram rules source} (mem : candidate ∈ options) :
    cost (options.foldl (CheckedProgram.preferBy cost) seed).program ≤ cost candidate.program := by
  induction options generalizing seed with
  | nil => exact (List.not_mem_nil mem).elim
  | cons head tail ih =>
    rcases List.mem_cons.mp mem with eq | h
    · subst candidate
      exact (fold_le_seed cost tail (CheckedProgram.preferBy cost seed head)).trans (prefer_right cost seed head)
    · exact ih (CheckedProgram.preferBy cost seed head) h

private theorem fold_mem (options : List (CheckedProgram rules source)) (seed : CheckedProgram rules source) :
    options.foldl (CheckedProgram.preferBy cost) seed = seed ∨ options.foldl (CheckedProgram.preferBy cost) seed ∈ options := by
  induction options generalizing seed with
  | nil => exact .inl rfl
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rcases ih (CheckedProgram.preferBy cost seed head) with eq | mem
    · rw [eq]
      unfold CheckedProgram.preferBy
      split
      · exact .inr List.mem_cons_self
      · exact .inl rfl
    · exact .inr (List.mem_cons_of_mem _ mem)

theorem search_fold_mem
    (next : ∀ p : RankedProgram P params results, List (CheckedProgram rules p))
    (fuel : Nat) (source : RankedProgram P params results) :
    (CheckedProgram.search next fuel source).foldl (CheckedProgram.preferBy cost)
      (CheckedProgram.identity rules source) ∈ CheckedProgram.search next fuel source := by
  rcases fold_mem cost (CheckedProgram.search next fuel source)
    (CheckedProgram.identity rules source) with eq | mem
  · rw [eq]
    cases fuel <;> exact List.mem_cons_self
  · exact mem

theorem optimize_mem [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (fuel : Nat) (source : Program P params out) :
    optimize eqPrim rs fuel source ∈ explore eqPrim rs fuel source :=
  search_fold_mem Program.cost (discover eqPrim rs) fuel source

end Silmaril.Proofs.SSA.Peggy.Optimizer
