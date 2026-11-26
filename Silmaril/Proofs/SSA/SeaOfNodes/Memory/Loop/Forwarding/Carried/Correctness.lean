module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Proofs

open RVSDG (Locals Origin Port Tuple)
open Memory.Forwarding (originKey originKey_injective)

variable {args : List ValueSort} {cells : Nat}
variable {past : List (List ValueSort)} {version : Nat}
variable {source : Loop.Graph args} {target : Graph args}

private theorem runWithLastStore_result (input : Tuple (Val cells) args)
    (body : Memory.Body args past version) (locals : Locals (Val cells) past)
    (heap : Heap cells) (last : Option Word) :
    (runWithLastStore input body locals heap last).result = body.denote input locals heap := by
  induction body generalizing heap last with
  | ret => rfl
  | load _ _ _ ih => exact ih _ _ _
  | store _ _ _ _ ih => exact ih _ _ _

theorem activateWithStore_result (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) :
    (graph.activateWithStore input header).result = graph.activate input header :=
  runWithLastStore_result input graph.body _ _ _

private theorem runWithLastStore_reads (observed : Port args .address) (input : Tuple (Val cells) args)
    (body : Memory.Body args past version) (locals : Locals (Val cells) past)
    (heap : Heap cells) (last : Option Word) (matched : Bool)
    (known : matched = true → last = some (heap.read (input.get observed)))
    (checked : lastStoreMatchesAt observed body matched = true) :
    let out := runWithLastStore input body locals heap last
    out.lastStored = some (out.result.2.read (input.get observed)) := by
  induction body generalizing heap last matched with
  | ret => exact known checked
  | load _ _ _ ih => exact ih _ _ _ _ known checked
  | store _ address value _ ih =>
    refine ih _ _ _ _ (fun found => ?_) checked
    have same : address = .arg observed := originKey_injective (beq_iff_eq.mp found)
    rw [same]
    exact congrArg some (Heap.read_write_same heap _ (readValue value input locals)).symm

private theorem accepted (success : rewrite source = some target) :
    ∃ memory : MemoryInput 0,
      source.body = .load memory (.arg target.address) target.body ∧
      target.stop = source.stop ∧
      lastStoreMatchesAt target.address target.body false = true := by
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

theorem lastStored_reads (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) :
    let out := target.activateWithStore input header
    out.lastStored = some (out.result.2.read (input.get target.address)) := by
  obtain ⟨_, _, _, checked⟩ := accepted success
  refine runWithLastStore_reads target.address input target.body _ _ none false ?_ checked
  intro impossible
  cases impossible

theorem step_agrees (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) (agrees : target.Agrees input header) :
    match target.step input header with
    | .inl result => source.step input header.heap = .inl result
    | .inr next => source.step input header.heap = .inr next.heap ∧ target.Agrees input next := by
  obtain ⟨_, bodyEq, stopEq, _⟩ := accepted success
  have same : target.activate input header = source.body.denote input header.heap := by
    rw [bodyEq]
    simp only [Graph.activate, Graph.Agrees] at agrees ⊢
    rw [agrees]
    rfl
  have cell := lastStored_reads success input header
  have test : target.stopWord input = source.stopWord input :=
    congrArg (fun (port : Port args .word) => (input.get port : Word)) stopEq
  dsimp only [Graph.step, Loop.Graph.step]
  rw [cell, activateWithStore_result, same, test]
  by_cases exit : (source.body.denote input header.heap).1 = source.stopWord input
  · simp only [ite_eq_left exit]
  · simp only [ite_eq_right exit, Graph.Agrees, Option.getD_some, true_and]

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
