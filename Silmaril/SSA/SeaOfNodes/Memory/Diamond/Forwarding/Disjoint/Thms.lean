module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Correctness

/-! # Finite return preservation through certified disjoint writes -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate args}

/-- A successful check for this occurrence supplies its own exported word
as a read of the exact addressed cell in its final heap. -/
theorem checkSlot_reads (graph : Graph args) (address : Port args .address) (candidate : Candidate args)
    (input : Tuple (Val cells) args) (arrival : Slot)
    (accepted : checkSlot graph address candidate input arrival = true) (initial : Heap cells) :
    let exported := (graph.arm (graph.merge.predecessor arrival)).denote input initial
    exported.2.read (input.get address) = exported.1 :=
  Proofs.checkSlot_reads graph address candidate input arrival accepted initial

/-- The actual latching occurrence determines the evidence used for the
post-join read. -/
theorem checkJoined_latch_reads (graph : Graph args) (address : Port args .address)
    (candidate : Candidate args) (input : Tuple (Val cells) args)
    (accepted : checkJoined graph address candidate input = true) (arrival : Slot) (edge : Projection)
    (initial : Heap cells) (selected : Word × Heap cells)
    (joined : latch graph.merge arrival (publish edge ((graph.arm edge).denote input initial)) = some selected) :
    selected.2.read (input.get address) = selected.1 :=
  Proofs.checkJoined_latch_reads graph address candidate input accepted arrival edge initial selected joined

theorem rewrite_denote (input : Tuple (Val cells) args) (success : rewrite graph candidate input = some rewritten)
    (guard : Bool) (initial : Heap cells) :
    rewritten.denote guard input initial = graph.denote guard input initial :=
  Proofs.rewrite_denote input success guard initial

/-- Success on the given address inputs preserves and reflects the return
word and entire final heap for either guard and any initial heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph candidate input = some rewritten)
    (guard : Bool) (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns guard input initial word final ↔ graph.Returns guard input initial word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewrite_denote input success]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint
