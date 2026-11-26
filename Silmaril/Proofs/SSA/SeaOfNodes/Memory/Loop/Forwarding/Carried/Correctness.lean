module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Proofs

open RVSDG (Tuple)
open Memory.Forwarding (checkExit checkExit_reads)

variable {args : List ValueSort} {cells : Nat}
variable {source : Loop.Graph args} {target : Graph args}

private theorem accepted (success : rewrite source = some target) :
    ∃ memory : MemoryInput 0,
      source.body = .load memory (.arg target.address) target.body ∧
      target.stop = source.stop ∧
      checkExit source.body target.address (finalVersion source.body) = true := by
  cases bodyEq : source.body with
  | ret => simp [rewrite, bodyEq] at success
  | store => simp [rewrite, bodyEq] at success
  | load memory address rest =>
    cases address with
    | output node _ => exact node.elim0
    | arg port =>
      simp only [rewrite, bodyEq] at success
      split at success
      next checked =>
        have eq := Option.some.inj success
        subst target
        exact ⟨memory, rfl, rfl, checked⟩
      next => cases success

theorem step_agrees (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) (agrees : target.Agrees input header) :
    match target.step input header with
    | .inl result => source.step input header.heap = .inl result
    | .inr next => source.step input header.heap = .inr next.heap ∧ target.Agrees input next := by
  obtain ⟨memory, bodyEq, stopEq, checked⟩ := accepted success
  have same : target.activate input header = source.body.denote input header.heap := by
    rw [bodyEq]
    simp only [Graph.activate, Graph.Agrees] at agrees ⊢
    rw [agrees]
    rfl
  have cell := checkExit_reads source.body target.address (finalVersion source.body) checked input header.heap
  unfold Graph.step Loop.Graph.step Graph.stopWord Loop.Graph.stopWord
  rw [same, stopEq]
  by_cases exit : (source.body.denote input header.heap).1 = (input.get source.stop : Word)
  · simp only [ite_eq_left exit]
  · simpa only [ite_eq_right exit, Graph.Agrees, true_and] using cell.symm

private theorem evalFrom_eq (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (count : Nat) (header : Header cells)
    (agrees : target.Agrees input header) :
    target.evalFrom input count header = source.evalFrom input count header.heap := by
  have relation := step_agrees success input header agrees
  cases taken : target.step input header with
  | inl result =>
    rw [taken] at relation
    cases count <;> simp only [Graph.evalFrom, Loop.Graph.evalFrom, taken, relation]
  | inr next =>
    rw [taken] at relation
    cases count with
    | zero => simp only [Graph.evalFrom, Loop.Graph.evalFrom, taken, relation.1]
    | succ count =>
      simpa only [Graph.evalFrom, Loop.Graph.evalFrom, taken, relation.1] using
        evalFrom_eq success input count next relation.2

theorem evalAfter_eq (success : rewrite source = some target) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) :
    target.evalAfter input initial count = source.evalAfter input initial count :=
  evalFrom_eq success input count (target.seed input initial) rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Proofs
