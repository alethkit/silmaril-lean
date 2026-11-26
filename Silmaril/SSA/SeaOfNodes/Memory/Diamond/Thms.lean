module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Correctness

/-! # Occurrence-indexed latching and finite execution agreement -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Merge Projection Slot)

universe u

/-- Latching succeeds exactly at the published edge's Region position and
returns its value. In particular it applies to a heap or a word/heap pair. -/
theorem latch_publish_iff {α : Type u} (merge : Merge) (arrival : Slot) (edge : Projection)
    (exported selected : α) :
    latch merge arrival (publish edge exported) = some selected ↔
      merge.predecessor arrival = edge ∧ exported = selected :=
  Proofs.latch_publish_iff merge arrival edge exported selected

/-- The arriving edge's own slot latches its exported value. -/
theorem latch_publish_slot {α : Type u} (merge : Merge) (edge : Projection) (value : α) :
    latch merge (merge.slot edge) (publish edge value) = some value :=
  Proofs.latch_publish_slot merge edge value

/-- Explicit-edge execution and heap threading agree on the word and final heap. -/
theorem Graph.returns_iff_denote {args : List ValueSort} {cells : Nat} (graph : Graph args)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells)
    (value : Word) (final : Heap cells) :
    graph.Returns guard input initial value final ↔
      graph.denote guard input initial = (value, final) :=
  Proofs.returns_iff_denote graph guard input initial value final

end Silmaril.SSA.SeaOfNodes.Memory.Diamond
