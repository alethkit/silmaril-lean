module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Proofs

open RVSDG (Locals Origin Port Tuple)
open Memory.Forwarding.Disjoint (Certificate cell)

variable {args : List ValueSort} {cells : Nat}
variable {past : List (List ValueSort)} {version : Nat}
variable {source : Loop.Graph args} {target : Graph args}
variable {requested : Nat} {facts : Certificate args}

private theorem runWithStore_result (input : Tuple (Val cells) args) (requested : Nat)
    (body : Memory.Body args past version) (locals : Locals (Val cells) past)
    (heap : Heap cells) (saved : Option Word) :
    (runWithStore input requested body locals heap saved).result = body.denote input locals heap := by
  induction body generalizing heap saved with
  | ret => rfl
  | load _ _ _ ih => exact ih _ _ _
  | store _ _ _ _ ih => exact ih _ _ _

theorem activateWithStore_result (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) :
    (graph.activateWithStore input header).result = graph.activate input header :=
  runWithStore_result input graph.storeVersion graph.body _ _ _

private theorem runWithStore_reads (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (body : Memory.Body args past version) (locals : Locals (Val cells) past)
    (heap : Heap cells) (saved : Option Word) (matched : Bool)
    (known : matched = true → saved = some (heap.read (cell input facts.observed)))
    (checked : storeSurvivesAt facts requested body matched = true) :
    let out := runWithStore input requested body locals heap saved
    out.stored = some (out.result.2.read (cell input facts.observed)) := by
  induction body generalizing heap saved matched with
  | ret => exact known checked
  | load _ _ _ ih => exact ih _ _ _ _ known checked
  | @store _ version _ address value _ ih =>
    by_cases selected : version + 1 = requested
    · simp only [storeSurvivesAt, ite_eq_left selected] at checked
      simp only [runWithStore]
      refine ih _ _ _ _ (fun found => ?_) checked
      simp only [ite_eq_left selected, facts.matches_read address found input locals]
      exact congrArg some (Heap.read_write_same heap _ (readValue value input locals)).symm
    · simp only [storeSurvivesAt, ite_eq_right selected] at checked
      simp only [runWithStore]
      refine ih _ _ _ _ (fun found => ?_) checked
      obtain ⟨previous, suffixCheck⟩ := Bool.and_eq_true_iff.mp found
      have covered := (Bool.and_eq_true_iff.mp suffixCheck).2
      simp only [ite_eq_right selected]
      exact (known previous).trans (congrArg some (Heap.read_write_other heap _ _
        (readValue value input locals) (facts.covers_read address covered input locals valid))).symm

private theorem accepted (success : rewriteWith source requested facts = some target) :
    ∃ (memory : MemoryInput 0) (address : Origin args [] .address),
      source.body = .load memory address target.body ∧ facts.matches address = true ∧
      target.stop = source.stop ∧ target.address = facts.observed ∧ target.storeVersion = requested ∧
      storeSurvivesAt facts requested target.body false = true := by
  cases bodyEq : source.body with
  | ret => simp [rewriteWith, bodyEq] at success
  | store => simp [rewriteWith, bodyEq] at success
  | load memory address rest =>
    simp only [rewriteWith, bodyEq] at success
    split at success
    next checked =>
      have eq := Option.some.inj success
      subst target
      obtain ⟨matched, survives⟩ := Bool.and_eq_true_iff.mp checked
      exact ⟨memory, address, rfl, matched, rfl, rfl, rfl, survives⟩
    next => cases success

theorem finalStore_witness (success : rewrite source = some target) (input : Tuple (Val cells) args) :
    ∃ certificate, rewriteWith source (finalVersion source.body) certificate = some target ∧
      certificate.Valid input := by
  cases bodyEq : source.body with
  | ret => simp [rewrite, bodyEq] at success
  | store => simp [rewrite, bodyEq] at success
  | load _ address _ =>
    cases address with
    | output node _ => exact node.elim0
    | arg port =>
      refine ⟨⟨port, []⟩, ?_, ?_⟩
      · simpa only [rewrite, bodyEq] using success
      · simp [Certificate.Valid]

theorem stored_reads (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (header : Header cells) :
    let out := target.activateWithStore input header
    out.stored = some (out.result.2.read (input.get target.address)) := by
  obtain ⟨_, _, _, _, _, addressEq, versionEq, checked⟩ := accepted success
  simp only [Graph.activateWithStore, addressEq, versionEq]
  refine runWithStore_reads input valid target.body _ _ none false ?_ checked
  intro impossible
  cases impossible

theorem step_agrees (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (header : Header cells) (agrees : target.Agrees input header) :
    match target.step input header with
    | .inl result => source.step input header.heap = .inl result
    | .inr next => source.step input header.heap = .inr next.heap ∧ target.Agrees input next := by
  obtain ⟨_, address, bodyEq, matched, stopEq, addressEq, _, _⟩ := accepted success
  have same : target.activate input header = source.body.denote input header.heap := by
    rw [bodyEq]
    simp only [Graph.activate, Graph.Agrees] at agrees ⊢
    simp only [Memory.Graph.denote, Memory.Body.denote, agrees, addressEq,
      facts.matches_read address matched input PUnit.unit, cell]
  have stored := stored_reads success input valid header
  have test : target.stopWord input = source.stopWord input :=
    congrArg (fun (port : Port args .word) => (input.get port : Word)) stopEq
  dsimp only [Graph.step, Loop.Graph.step]
  rw [stored, activateWithStore_result, same, test]
  by_cases exit : (source.body.denote input header.heap).1 = source.stopWord input
  · simp only [ite_eq_left exit]
  · simp only [ite_eq_right exit, Graph.Agrees, Option.getD_some, true_and]

private theorem evalFrom_eq (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (count : Nat) (header : Header cells)
    (agrees : target.Agrees input header) :
    target.evalFrom input count header = source.evalFrom input count header.heap := by
  have relation := step_agrees success input valid header agrees
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
        evalFrom_eq success input valid count next relation.2

theorem evalAfter_eq (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells) (count : Nat) :
    target.evalAfter input initial count = source.evalAfter input initial count :=
  evalFrom_eq success input valid count (target.seed input initial) rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Proofs
