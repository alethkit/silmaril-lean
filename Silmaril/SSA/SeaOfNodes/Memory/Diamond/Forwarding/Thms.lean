module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Correctness

/-! # Joined forwarding preserves the word and whole heap -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate}

/-- At either incoming occurrence, the checked word equals a read from that
occurrence's final heap at the shared Load address. -/
theorem checkJoined_reads (graph : Graph args) (address : Port args .address) (candidate : Candidate)
    (accepted : checkJoined graph address candidate = true) (arrival : Slot)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    let exported := (graph.arm (graph.merge.predecessor arrival)).denote input initial
    exported.2.read (input.get address) = exported.1 :=
  Proofs.checkJoined_reads graph address candidate accepted arrival input initial

/-- Latching the word and memory from the actual arriving occurrence gives
the exact value of the post-join Load. -/
theorem checkJoined_latch_reads (graph : Graph args) (address : Port args .address) (candidate : Candidate)
    (accepted : checkJoined graph address candidate = true) (arrival : Slot) (edge : Projection)
    (input : Tuple (Val cells) args) (initial : Heap cells) (selected : Word × Heap cells)
    (joined : latch graph.merge arrival (publish edge ((graph.arm edge).denote input initial)) = some selected) :
    selected.2.read (input.get address) = selected.1 :=
  Proofs.checkJoined_latch_reads graph address candidate accepted arrival edge input initial selected joined

theorem rewrite_denote (success : rewrite graph candidate = some rewritten)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    rewritten.denote guard input initial = graph.denote guard input initial :=
  Proofs.rewrite_denote success guard input initial

/-- A successful rewrite preserves and reflects the full source observation
under either Boolean guard. -/
theorem rewrite_returns_iff (success : rewrite graph candidate = some rewritten)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) (value : Word) (final : Heap cells) :
    rewritten.Returns guard input initial value final ↔ graph.Returns guard input initial value final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewrite_denote success]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding
