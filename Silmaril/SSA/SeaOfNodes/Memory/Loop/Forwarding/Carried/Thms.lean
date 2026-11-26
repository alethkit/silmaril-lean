module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {source : Loop.Graph args} {target : Graph args}

/-- The entry read establishes the scalar Φ invariant for any initial heap. -/
theorem Graph.seed_agrees (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    graph.Agrees input (graph.seed input initial) :=
  rfl

/-- Retaining the Store operand preserves the ordinary returned word and heap. -/
theorem Graph.activateWithStore_result (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) :
    (graph.activateWithStore input header).result = graph.activate input header :=
  Proofs.activateWithStore_result graph input header

/-- An admitted activation obtains its feedback word from the last Store,
which agrees with the addressed cell of the entire resulting heap. -/
theorem rewrite_lastStored_reads (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) :
    let out := target.activateWithStore input header
    out.lastStored = some (out.result.2.read (input.get target.address)) :=
  Proofs.lastStored_reads success input header

/-- Each activation makes the same exit or backedge. On a backedge the
checked Store ensures that the supplied word agrees with the new heap. -/
theorem rewrite_step_agrees (success : rewrite source = some target)
    (input : Tuple (Val cells) args) (header : Header cells) (agrees : target.Agrees input header) :
    match target.step input header with
    | .inl result => source.step input header.heap = .inl result
    | .inr next => source.step input header.heap = .inr next.heap ∧ target.Agrees input next :=
  Proofs.step_agrees success input header agrees

theorem rewrite_evalAfter (success : rewrite source = some target) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) :
    target.evalAfter input initial count = source.evalAfter input initial count :=
  Proofs.evalAfter_eq success input initial count

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
