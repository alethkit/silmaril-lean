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

private theorem suffix_denote (check : Port args .address → Bool)
    (source rewritten : Memory.Graph (.word :: args))
    (ok : rewriteSuffixUsing check source = some rewritten)
    (input : Tuple (Val cells) args) (selected : Word × Heap cells)
    (reads : ∀ address, check address = true → selected.2.read (input.get address) = selected.1) :
    rewritten.denote (.cons selected.1 input) selected.2 =
      source.denote (.cons selected.1 input) selected.2 := by
  cases source with
  | ret => simp [rewriteSuffixUsing] at ok
  | store => simp [rewriteSuffixUsing] at ok
  | load memory wire rest =>
    cases wire with
    | output i _ => exact i.elim0
    | arg port =>
      cases port with
      | tail address =>
        by_cases accepted : check address = true
        · have equal : Memory.Forwarding.rewire rest (Memory.Forwarding.dropLoad (.arg .head)) = rewritten := by
            simpa [rewriteSuffixUsing, accepted] using ok
          subst rewritten
          exact Memory.Forwarding.replaceLoad_denote memory (.arg (.tail address)) rest (.arg .head)
            (.cons selected.1 input) PUnit.unit selected.2 (reads address accepted)
        · simp [rewriteSuffixUsing, accepted] at ok

theorem rewriteUsing_denote {graph rewritten : Graph args} {check : Port args .address → Bool}
    (success : rewriteUsing graph check = some rewritten)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells)
    (reads : ∀ address, check address = true →
      let selected := (graph.arm (Projection.ofBool guard)).denote input initial
      selected.2.read (input.get address) = selected.1) :
    rewritten.denote guard input initial = graph.denote guard input initial := by
  obtain ⟨body, ok, rfl⟩ := Option.map_eq_some_iff.mp success
  exact suffix_denote check graph.suffix body ok input ((graph.arm (Projection.ofBool guard)).denote input initial) reads

theorem rewrite_denote {graph rewritten : Graph args} {candidate : Candidate}
    (success : rewrite graph candidate = some rewritten)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    rewritten.denote guard input initial = graph.denote guard input initial := by
  refine rewriteUsing_denote success guard input initial ?_
  intro address accepted
  let edge := Projection.ofBool guard
  let selected := (graph.arm edge).denote input initial
  exact checkJoined_latch_reads graph address candidate accepted (graph.merge.slot edge) edge
    input initial selected (latch_publish_slot graph.merge edge selected)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Proofs
