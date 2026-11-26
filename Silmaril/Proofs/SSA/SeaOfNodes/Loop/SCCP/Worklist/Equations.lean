module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

private theorem incoming_ne_exit (via : Incoming) : incomingIndex via ≠ exitIndex := by
  cases via <;> decide

theorem evaluate_eq (job : Task) (state : State m.value carried out) :
    evaluate m g input job (dependencies state job) = get (SCCP.transfer m g input state) job := by
  cases job with
  | control =>
    by_cases marked : incomingIndex .entry ∈ state.1 <;>
      simp [dependencies, evaluate, get, transfer, control, marked] <;> rfl
  | phi =>
    funext i
    by_cases marked : incomingIndex .backedge ∈ state.1 <;>
      simp [dependencies, evaluate, get, transfer, marked, phiFacts, phiFact, gate, incoming_ne_exit]
  | result =>
    by_cases marked : exitIndex ∈ state.1 <;>
      simp [dependencies, evaluate, get, transfer, gate, marked] <;> rfl

theorem get_update_self (job : Task) (state : State m.value carried out) :
    get (update m g input job state) job = get (SCCP.transfer m g input state) job := by
  have evaluated := evaluate_eq (m := m) (g := g) (input := input) job state
  cases job with
  | control => exact evaluated
  | phi => exact evaluated
  | result => exact evaluated

theorem get_update_other (job reader : Task) (state : State m.value carried out) (different : reader ≠ job) :
    get (update m g input job state) reader = get state reader := by
  cases job <;> cases reader <;> first | rfl | contradiction

theorem eq_of_get {lhs rhs : State value carried out}
    (eq : ∀ job, get lhs job = get rhs job) : lhs = rhs :=
  Prod.ext (congrArg ULift.down (eq .control)) (Prod.ext (eq .phi) (eq .result))

private theorem update_eq (job : Task) (state : State m.value carried out) :
    update m g input job state = set state job (get (SCCP.transfer m g input state) job) := by
  unfold update
  rw [evaluate_eq]

theorem le_update (job : Task) (state : State m.value carried out) (le : state ≤ SCCP.transfer m g input state) :
    state ≤ update m g input job state := by
  rw [update_eq]
  cases job with
  | control => exact ⟨le.1, le_rfl⟩
  | phi => exact ⟨le_rfl, le.2.1, le_rfl⟩
  | result => exact ⟨le_rfl, le_rfl, le.2.2⟩

theorem update_le (job : Task) {state upper : State m.value carried out}
    (le : state ≤ upper) (rhs : SCCP.transfer m g input state ≤ upper) :
    update m g input job state ≤ upper := by
  rw [update_eq]
  cases job with
  | control => exact ⟨rhs.1, le.2⟩
  | phi => exact ⟨le.1, rhs.2.1, le.2.2⟩
  | result => exact ⟨le.1, le.2.1, rhs.2.2⟩

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Proofs
