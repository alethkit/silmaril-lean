module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Correctness

/-! # Exact backedge counts and finite whole-heap observations -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}

/-- A counted explicit-edge run returns exactly the observation of the
heap-threaded evaluator at that backedge count. -/
theorem Graph.returnsAfter_iff_evalAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) (value : Word) (final : Heap cells) :
    graph.ReturnsAfter input initial count value final ↔
      graph.evalAfter input initial count = some (value, final) :=
  Proofs.returnsAfter_iff_evalAfter graph input initial count value final

/-- The partial denotation preserves and reflects the word and entire heap
of each finite source return. -/
theorem Graph.returns_iff_mem_denote (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input initial value final ↔ (value, final) ∈ graph.denote input initial :=
  Proofs.returns_iff_mem_denote graph input initial value final

end Silmaril.SSA.SeaOfNodes.Memory.Loop
