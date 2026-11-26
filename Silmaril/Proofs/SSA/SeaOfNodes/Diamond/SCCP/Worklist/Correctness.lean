module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Proofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [DecidableEq (sortValue m.value out)]
variable {g : Graph Op inputs sigs out} {entry : Tuple (Fact m.value) (dataPorts inputs)}

private theorem mem_schedule {changed : Prop} [Decidable changed] {job task : Task} {pending : List Task}
    (old : job ∈ pending) : job ∈ schedule changed task pending := by
  unfold schedule
  split <;> simp [old]

private theorem triggered_mem {changed : Prop} [Decidable changed] {task : Task} {pending : List Task}
    (trigger : changed) : task ∈ schedule changed task pending := by
  by_cases present : task ∈ pending <;> simp [schedule, trigger, present]

private theorem unchanged_of_absent {α : Type*} [DecidableEq α] {before after : α}
    {task : Task} {pending : List Task} (absent : task ∉ schedule (after ≠ before) task pending) :
    after = before := by
  by_contra changed
  exact absent (triggered_mem changed)

private theorem potential_append (pending : List Task) (task : Task) :
    potential (pending ++ [task]) = potential pending + task.weight := by
  induction pending with
  | nil => simp [potential]
  | cons _ _ ih => simp [potential, ih, Nat.add_assoc]

private theorem potential_schedule (changed : Prop) [Decidable changed] (task : Task) (pending : List Task) :
    potential (schedule changed task pending) ≤ potential pending + task.weight := by
  unfold schedule
  split <;> simp [potential_append]

theorem step_decreases (task : Task) (state : State m.value sigs out) (pending : List Task) :
    potential (step m g entry task state pending).2 < potential (task :: pending) := by
  rcases state with ⟨edges, facts, result⟩
  cases task with
  | producers =>
    let wakeBranch := predicateFact g entry (producerFacts m g entry) ≠ predicateFact g entry facts
    let wakePhi := phiInputs g entry edges (producerFacts m g entry) ≠ phiInputs g entry edges facts
    let next := schedule wakeBranch .branch pending
    change potential (schedule wakePhi .phi next) < 4 + potential pending
    have branchBudget := potential_schedule wakeBranch .branch pending
    have phiBudget := potential_schedule wakePhi .phi next
    change potential next ≤ potential pending + 2 at branchBudget
    change potential (schedule wakePhi .phi next) ≤ potential next + 1 at phiBudget
    omega
  | branch =>
    have phiBudget := potential_schedule
      (branchEdges g.phi.merge (predicateFact g entry facts) ≠ edges) .phi pending
    change potential (schedule _ .phi pending) < 2 + potential pending
    change potential (schedule _ .phi pending) ≤ potential pending + 1 at phiBudget
    omega
  | phi =>
    change potential pending < 1 + potential pending
    omega

private theorem runSteps_drains (fuel : Nat) (state : State m.value sigs out) (pending : List Task)
    (budget : potential pending ≤ fuel) : (runSteps m g entry fuel state pending).pending = [] := by
  induction fuel generalizing state pending with
  | zero =>
    cases pending with
    | nil => rfl
    | cons task rest =>
      have positive : 0 < task.weight := by cases task <;> decide
      simp only [potential] at budget
      omega
  | succ fuel ih =>
    cases pending with
    | nil => rfl
    | cons task rest =>
      have next := Nat.lt_succ_iff.mp ((step_decreases (g := g) (entry := entry) task state rest).trans_le budget)
      exact ih _ _ next

theorem run_drains : (run m g entry).pending = [] :=
  runSteps_drains _ _ _ le_rfl

private def Holds (task : Task) (state : State m.value sigs out) : Prop :=
  match task with
  | .producers => (transfer m g entry state).2.1 = state.2.1
  | .branch => (transfer m g entry state).1 = state.1
  | .phi => (transfer m g entry state).2.2 = state.2.2

private def Stable (state : State m.value sigs out) (pending : List Task) : Prop :=
  ∀ task, task ∉ pending → Holds (g := g) (entry := entry) task state

private theorem phiFact_eq_of_inputs {edges : Executable} {a b : ProducerFacts m.value (RVSDG.extend [] sigs)}
    (h : phiInputs g entry edges a = phiInputs g entry edges b) :
    phiFact g.phi edges entry a = phiFact g.phi edges entry b :=
  congrArg (fun pair : Semantics.Dataflow.Flat (sortValue m.value out) × _ => pair.1.join pair.2) h

private theorem step_stable {task : Task} {state : State m.value sigs out} {pending : List Task}
    (stable : Stable (g := g) (entry := entry) state (task :: pending)) :
    Stable (g := g) (entry := entry) (step m g entry task state pending).1
      (step m g entry task state pending).2 := by
  rcases state with ⟨edges, facts, result⟩
  intro job absent
  cases task with
  | producers =>
    let new := producerFacts m g entry
    let next := schedule (predicateFact g entry new ≠ predicateFact g entry facts) .branch pending
    change job ∉ schedule (phiInputs g entry edges new ≠ phiInputs g entry edges facts) .phi next at absent
    have absentNext : job ∉ next := fun old => absent (mem_schedule old)
    have absentPending : job ∉ pending := fun old => absentNext (mem_schedule old)
    cases job with
    | producers => rfl
    | branch =>
      have eq := unchanged_of_absent absentNext
      have old := stable .branch (by simp [absentPending])
      change branchEdges g.phi.merge (predicateFact g entry facts) = edges at old
      change branchEdges g.phi.merge (predicateFact g entry new) = edges
      rw [eq, old]
    | phi =>
      have eq := phiFact_eq_of_inputs (unchanged_of_absent absent)
      have old := stable .phi (by simp [absentPending])
      exact eq.trans old
  | branch =>
    let new := branchEdges g.phi.merge (predicateFact g entry facts)
    change job ∉ schedule (new ≠ edges) .phi pending at absent
    have absentPending : job ∉ pending := fun old => absent (mem_schedule old)
    cases job with
    | producers => exact stable .producers (by simp [absentPending])
    | branch => rfl
    | phi =>
      have eq := unchanged_of_absent absent
      have old := stable .phi (by simp [absentPending])
      change phiFact g.phi new entry facts = result
      rw [eq]
      exact old
  | phi =>
    cases job with
    | producers => exact stable .producers (by simp [show Task.producers ∉ pending from absent])
    | branch => exact stable .branch (by simp [show Task.branch ∉ pending from absent])
    | phi => rfl

private theorem step_le_of_fixed (task : Task) (state upper : State m.value sigs out) (pending : List Task)
    (fixed : transfer m g entry upper = upper) (le : state ≤ upper) :
    (step m g entry task state pending).1 ≤ upper := by
  rcases state with ⟨edges, facts, result⟩
  have checked := (transfer_mono m g entry le).trans fixed.le
  cases task with
  | producers => exact ⟨le.1, checked.2.1, le.2.2⟩
  | branch => exact ⟨checked.1, le.2⟩
  | phi => exact ⟨le.1, le.2.1, checked.2.2⟩

private theorem runSteps_invariants (fuel : Nat) (state upper : State m.value sigs out) (pending : List Task)
    (fixed : transfer m g entry upper = upper) (le : state ≤ upper)
    (stable : Stable (g := g) (entry := entry) state pending) :
    let result := runSteps m g entry fuel state pending
    result.state ≤ upper ∧ Stable (g := g) (entry := entry) result.state result.pending := by
  induction fuel generalizing state pending with
  | zero => cases pending <;> exact ⟨le, stable⟩
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨le, stable⟩
    | cons task rest => exact ih _ _ (step_le_of_fixed task state upper rest fixed le) (step_stable stable)

private theorem initial_stable : Stable (g := g) (entry := entry) ⊥ initial := by
  intro task absent
  cases task with
  | producers => simp [initial] at absent
  | branch => simp [initial] at absent
  | phi => rfl

theorem solve_eq_simultaneous : solve m g entry = SCCP.solve m g entry := by
  let result := run m g entry
  have invariants : result.state ≤ SCCP.solve m g entry ∧
      Stable (g := g) (entry := entry) result.state result.pending :=
    runSteps_invariants _ _ _ _ (solve_fixed m g entry) bot_le initial_stable
  have stable := invariants.2
  rw [run_drains (m := m) (g := g) (entry := entry)] at stable
  have fixed : transfer m g entry result.state = result.state := Prod.ext
    (stable .branch (by simp))
    (Prod.ext (stable .producers (by simp)) (stable .phi (by simp)))
  exact le_antisymm invariants.1 ((solve_isLeast m g entry).2 fixed)

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Proofs
