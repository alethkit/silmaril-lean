module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {source : Loop.Graph args} {target : Graph args}
variable {requested : Nat} {facts : Certificate args}

/-- The entry read establishes the scalar Φ invariant for any initial heap. -/
theorem Graph.seed_agrees (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    graph.Agrees input (graph.seed input initial) :=
  rfl

/-- Retaining the Store operand preserves the ordinary returned word and heap. -/
theorem Graph.activateWithStore_result (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) :
    (graph.activateWithStore input header).result = graph.activate input header :=
  Proofs.activateWithStore_result graph input header

/-- The executable invocation check enforces the certificate's concrete inequalities. -/
theorem rewriteChecked_eq_some_iff (input : Tuple (Val cells) args) :
    rewriteChecked source requested facts input = some target ↔
      rewriteWith source requested facts = some target ∧ facts.Valid input := by
  simp only [rewriteChecked, ← facts.check_iff_valid input]
  split <;> simp_all

/-- On every satisfying invocation, the selected Store's actual word
agrees with the observed cell after the entire suffix. -/
theorem rewriteWith_stored_reads (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (header : Header cells) :
    let out := target.activateWithStore input header
    out.stored = some (out.result.2.read (input.get target.address)) :=
  Proofs.stored_reads success input valid header

theorem rewriteWith_step_agrees (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (header : Header cells) (agrees : target.Agrees input header) :
    match target.step input header with
    | .inl result => source.step input header.heap = .inl result
    | .inr next => source.step input header.heap = .inr next.heap ∧ target.Agrees input next :=
  Proofs.step_agrees success input valid header agrees

theorem rewriteWith_evalAfter (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells) (count : Nat) :
    target.evalAfter input initial count = source.evalAfter input initial count :=
  Proofs.evalAfter_eq success input valid initial count

theorem rewriteWith_returnsAfter_iff (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    target.evalAfter input initial count = some (word, final) ↔
      source.ReturnsAfter input initial count word final := by
  rw [rewriteWith_evalAfter success input valid, source.returnsAfter_iff_evalAfter]

theorem rewriteWith_returns_iff (success : rewriteWith source requested facts = some target)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    target.Returns input initial word final ↔ source.Returns input initial word final :=
  exists_congr (fun count => rewriteWith_returnsAfter_iff success input valid initial count word final)

/-- An admitted activation obtains its feedback word from the last Store,
which agrees with the addressed cell of the entire resulting heap. -/
theorem rewrite_lastStored_reads (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) :
    let out := target.activateWithStore input header
    out.stored = some (out.result.2.read (input.get target.address)) := by
  obtain ⟨_, checked, valid⟩ := Proofs.finalStore_witness success input
  exact rewriteWith_stored_reads checked input valid header

/-- Each activation makes the same exit or backedge. On a backedge the
checked Store ensures that the supplied word agrees with the new heap. -/
theorem rewrite_step_agrees (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) (agrees : target.Agrees input header) :
    match target.step input header with
    | .inl result => source.step input header.heap = .inl result
    | .inr next => source.step input header.heap = .inr next.heap ∧ target.Agrees input next := by
  obtain ⟨_, checked, valid⟩ := Proofs.finalStore_witness success input
  exact rewriteWith_step_agrees checked input valid header agrees

theorem rewrite_evalAfter (success : rewrite source = some target) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) :
    target.evalAfter input initial count = source.evalAfter input initial count := by
  obtain ⟨_, checked, valid⟩ := Proofs.finalStore_witness success input
  exact rewriteWith_evalAfter checked input valid initial count

/-- Counted target execution agrees with explicit source edges on the
returned word and entire heap. -/
theorem rewrite_returnsAfter_iff (success : rewrite source = some target) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    target.evalAfter input initial count = some (word, final) ↔
      source.ReturnsAfter input initial count word final := by
  rw [rewrite_evalAfter success, source.returnsAfter_iff_evalAfter]

theorem rewrite_returns_iff (success : rewrite source = some target) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    target.Returns input initial word final ↔ source.Returns input initial word final :=
  exists_congr (fun count => rewrite_returnsAfter_iff success input initial count word final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried
