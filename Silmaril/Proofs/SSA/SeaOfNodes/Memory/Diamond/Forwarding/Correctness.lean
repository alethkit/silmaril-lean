module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Proofs

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}

theorem checkJoined_reads (graph : Graph args) (address : Port args .address) (candidate : Candidate)
    (accepted : checkJoined graph address candidate = true) (arrival : Slot)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    let exported := (graph.arm (graph.merge.predecessor arrival)).denote input initial
    exported.2.read (input.get address) = exported.1 := by
  obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp accepted
  cases arrival with
  | first => exact Memory.Forwarding.checkExit_reads _ address candidate.firstStore first input initial
  | second => exact Memory.Forwarding.checkExit_reads _ address candidate.secondStore second input initial

theorem checkJoined_latch_reads (graph : Graph args) (address : Port args .address) (candidate : Candidate)
    (accepted : checkJoined graph address candidate = true) (arrival : Slot) (edge : Projection)
    (input : Tuple (Val cells) args) (initial : Heap cells) (selected : Word × Heap cells)
    (joined : latch graph.merge arrival (publish edge ((graph.arm edge).denote input initial)) = some selected) :
    selected.2.read (input.get address) = selected.1 := by
  obtain ⟨arrived, rfl⟩ := (latch_publish_iff graph.merge arrival edge _ selected).mp joined
  simpa only [arrived] using checkJoined_reads graph address candidate accepted arrival input initial

private theorem suffix_denote (graph : Graph args) (candidate : Candidate)
    (source rewritten : Memory.Graph (.word :: args))
    (ok : rewriteSuffix graph candidate source = some rewritten)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    let selected := (graph.arm (Projection.ofBool guard)).denote input initial
    rewritten.denote (.cons selected.1 input) selected.2 =
      source.denote (.cons selected.1 input) selected.2 := by
  cases source with
  | ret => simp [rewriteSuffix] at ok
  | store => simp [rewriteSuffix] at ok
  | load memory wire rest =>
    cases wire with
    | output i _ => exact i.elim0
    | arg port =>
      cases port with
      | tail address =>
        by_cases accepted : checkJoined graph address candidate = true
        · have equal : Memory.Forwarding.rewire rest (Memory.Forwarding.dropLoad (.arg .head)) = rewritten := by
            simpa [rewriteSuffix, accepted] using ok
          subst rewritten
          let edge := Projection.ofBool guard
          let selected := (graph.arm edge).denote input initial
          have reads : selected.2.read (input.get address) = selected.1 :=
            checkJoined_latch_reads graph address candidate accepted (graph.merge.slot edge) edge
              input initial selected (latch_publish_slot graph.merge edge selected)
          exact Memory.Forwarding.replaceLoad_denote memory (.arg (.tail address)) rest (.arg .head)
            (.cons selected.1 input) PUnit.unit selected.2 reads
        · simp [rewriteSuffix, accepted] at ok

theorem rewrite_denote {graph rewritten : Graph args} {candidate : Candidate}
    (success : rewrite graph candidate = some rewritten)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    rewritten.denote guard input initial = graph.denote guard input initial := by
  obtain ⟨body, ok, rfl⟩ := Option.map_eq_some_iff.mp success
  exact suffix_denote graph candidate graph.suffix body ok guard input initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Proofs
