module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Proofs

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}

theorem checkSlot_reads (graph : Graph args) (address : Port args .address) (candidate : Candidate args)
    (input : Tuple (Val cells) args) (arrival : Slot)
    (accepted : checkSlot graph address candidate input arrival = true) (initial : Heap cells) :
    let exported := (graph.arm (graph.merge.predecessor arrival)).denote input initial
    exported.2.read (input.get address) = exported.1 := by
  obtain ⟨valid, matched⟩ := Bool.and_eq_true_iff.mp accepted
  exact Memory.Forwarding.Disjoint.checkExitWith_reads _ _ matched input initial
    ((Memory.Forwarding.Disjoint.Certificate.check_iff_valid _ input).mp valid)

theorem checkJoined_latch_reads (graph : Graph args) (address : Port args .address)
    (candidate : Candidate args) (input : Tuple (Val cells) args)
    (accepted : checkJoined graph address candidate input = true) (arrival : Slot) (edge : Projection)
    (initial : Heap cells) (selected : Word × Heap cells)
    (joined : latch graph.merge arrival (publish edge ((graph.arm edge).denote input initial)) = some selected) :
    selected.2.read (input.get address) = selected.1 := by
  have checked : checkSlot graph address candidate input arrival = true := by
    obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp accepted
    cases arrival
    · exact first
    · exact second
  obtain ⟨arrived, rfl⟩ := (latch_publish_iff graph.merge arrival edge _ selected).mp joined
  simpa only [arrived] using checkSlot_reads graph address candidate input arrival checked initial

theorem rewrite_denote {graph rewritten : Graph args} {candidate : Candidate args}
    (input : Tuple (Val cells) args) (success : rewrite graph candidate input = some rewritten)
    (guard : Bool) (initial : Heap cells) :
    rewritten.denote guard input initial = graph.denote guard input initial := by
  refine Memory.Diamond.Forwarding.rewriteUsing_denote success guard input initial ?_
  intro address accepted
  let edge := Projection.ofBool guard
  let selected := (graph.arm edge).denote input initial
  exact checkJoined_latch_reads graph address candidate input accepted (graph.merge.slot edge) edge
    initial selected (latch_publish_slot graph.merge edge selected)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Proofs
