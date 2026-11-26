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
variable {params : List (PEG.Ty Data)} {out : PEG.Ty Data}
variable {p : Program P params out} {r : Rule P out} {rs : List (Rule P out)}

theorem match_sound (found : RootMatch p r) (M : Core.Model (signature P))
    (env : ∀ i, M.carrier (context params i)) (law : r.core.Holds M)
    (guards : ∀ e ∈ r.guards,
      (Core.Pattern.instantiate (termSub found.binding) e.lhs).eval M env =
        (Core.Pattern.instantiate (termSub found.binding) e.rhs).eval M env) :
    (encodeOutputs p.ranked 0).eval M env =
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

private theorem prefer_left (left right : Candidate rs p) :
    (prefer left right).program.cost ≤ left.program.cost := by
  unfold prefer
  split
  next h => exact Nat.le_of_lt h
  next => exact Nat.le_refl _

private theorem prefer_right (left right : Candidate rs p) :
    (prefer left right).program.cost ≤ right.program.cost := by
  unfold prefer
  split
  next => exact Nat.le_refl _
  next h => exact Nat.le_of_not_gt h

private theorem fold_le_seed (options : List (Candidate rs p)) (seed : Candidate rs p) :
    (options.foldl prefer seed).program.cost ≤ seed.program.cost := by
  induction options generalizing seed with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact (ih (prefer seed head)).trans (prefer_left seed head)

theorem fold_le_member (options : List (Candidate rs p)) (seed : Candidate rs p)
    {candidate : Candidate rs p} (mem : candidate ∈ options) :
    (options.foldl prefer seed).program.cost ≤ candidate.program.cost := by
  induction options generalizing seed with
  | nil => exact (List.not_mem_nil mem).elim
  | cons head tail ih =>
    rcases List.mem_cons.mp mem with eq | h
    · subst candidate
      exact (fold_le_seed tail (prefer seed head)).trans (prefer_right seed head)
    · exact ih (prefer seed head) h

private theorem fold_mem (options : List (Candidate rs p)) (seed : Candidate rs p) :
    options.foldl prefer seed = seed ∨ options.foldl prefer seed ∈ options := by
  induction options generalizing seed with
  | nil => exact .inl rfl
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rcases ih (prefer seed head) with eq | mem
    · rw [eq]
      unfold prefer
      split
      · exact .inr List.mem_cons_self
      · exact .inl rfl
    · exact .inr (List.mem_cons_of_mem _ mem)

theorem optimize_mem [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (fuel : Nat) (source : Program P params out) :
    optimize eqPrim rs fuel source ∈ explore eqPrim rs fuel source := by
  rcases fold_mem (explore eqPrim rs fuel source) (Candidate.identity rs source) with eq | mem
  · change optimize eqPrim rs fuel source = _ at eq
    rw [eq]
    cases fuel <;> exact List.mem_cons_self
  · exact mem

end Silmaril.Proofs.SSA.Peggy.Optimizer
