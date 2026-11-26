module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Equations
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Queue

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

private def Stable (state : State m.value carried out) (pending : List Task) : Prop :=
  ∀ task, task ∉ pending → get (SCCP.transfer m g input state) task = get state task

private theorem stable_step (job : Task) (state : State m.value carried out) (pending : List Task)
    (stable : Stable (g := g) (input := input) state (job :: pending)) :
    Stable (g := g) (input := input) (step m g input job state pending).1
      (step m g input job state pending).2 := by
  let new := update m g input job state
  intro reader absent
  have same : dependencies new reader = dependencies state reader := by
    by_contra changed
    exact absent (changed_mem_wake changed)
  have rhs := congrArg (evaluate m g input reader) same
  rw [evaluate_eq, evaluate_eq] at rhs
  by_cases current : reader = job
  · subst reader
    exact rhs.trans (get_update_self job state).symm
  · have tailAbsent : reader ∉ pending := fun h => absent (mem_wake h)
    have old := stable reader (by simp [current, tailAbsent])
    exact rhs.trans (old.trans (get_update_other job reader state current).symm)

private theorem ascending_step (job : Task) (state : State m.value carried out)
    (ascending : state ≤ SCCP.transfer m g input state) :
    update m g input job state ≤ SCCP.transfer m g input (update m g input job state) :=
  (update_le job ascending le_rfl).trans (transfer_mono m g input (le_update job state ascending))

theorem step_decreases (job : Task) (state : State m.value carried out) (pending : List Task)
    (ascending : state ≤ SCCP.transfer m g input state) :
    potential (step m g input job state pending).1 (step m g input job state pending).2 <
      potential state (job :: pending) := by
  let new := update m g input job state
  change potential new (wake state new pending) < potential state (job :: pending)
  by_cases equal : new = state
  · rw [equal, wake_same]
    simp [potential]
  · let ranks := height m.value carried out
    have grown : state < new := lt_of_le_of_ne (le_update job state ascending) (fun h => equal h.symm)
    have strict := ranks.rank_strict grown
    have bound := ranks.rank_le new
    have size := wake_length state new pending
    change (ranks.bound - ranks.rank new) * 4 + (wake state new pending).length <
      (ranks.bound - ranks.rank state) * 4 + (pending.length + 1)
    omega

theorem step_nodup (job : Task) (state : State m.value carried out) {pending : List Task}
    (nodup : pending.Nodup) : (step m g input job state pending).2.Nodup :=
  wake_nodup state (update m g input job state) nodup

private theorem runSteps_checked (fuel : Nat) (state upper : State m.value carried out) (pending : List Task)
    (fixed : SCCP.transfer m g input upper = upper) (ascending : state ≤ SCCP.transfer m g input state)
    (below : state ≤ upper) (stable : Stable (g := g) (input := input) state pending)
    (budget : potential state pending ≤ fuel) :
    let result := runSteps m g input fuel state pending
    result.pending = [] ∧ result.state ≤ upper ∧ Stable (g := g) (input := input) result.state result.pending := by
  induction fuel generalizing state pending with
  | zero =>
    cases pending with
    | nil => exact ⟨rfl, below, stable⟩
    | cons job rest =>
      simp only [potential, List.length_cons] at budget
      omega
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨rfl, below, stable⟩
    | cons job rest =>
      have nextBudget := Nat.lt_succ_iff.mp ((step_decreases job state rest ascending).trans_le budget)
      have rhsBelow := (transfer_mono m g input below).trans fixed.le
      exact ih _ _ (ascending_step job state ascending) (update_le job below rhsBelow)
        (stable_step job state rest stable) nextBudget

private theorem initial_stable : Stable (g := g) (input := input) ⊥ initial := by
  intro job absent
  cases job with
  | control => simp [initial] at absent
  | phi => rfl
  | result => rfl

attribute [local irreducible] SCCP.solve

theorem run_spec : (run m g input).pending = [] ∧ solve m g input = SCCP.solve m g input := by
  let result := run m g input
  have final : result.pending = [] ∧ result.state ≤ SCCP.solve m g input ∧
      Stable (g := g) (input := input) result.state result.pending :=
    runSteps_checked _ _ _ _ (solve_fixed m g input) bot_le bot_le initial_stable le_rfl
  have stable := final.2.2
  rw [final.1] at stable
  have fixed : SCCP.transfer m g input result.state = result.state :=
    eq_of_get (fun job => stable job (by simp))
  exact ⟨final.1, le_antisymm final.2.1 ((solve_isLeast m g input).2 fixed)⟩

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Proofs
