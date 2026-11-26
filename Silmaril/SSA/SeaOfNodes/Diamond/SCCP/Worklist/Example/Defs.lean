module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Thms

/-! Queue traces and wakeups on the shared-producer SCCP diamond. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example

open Semantics.Dataflow (Flat)
open SCCP.Example (graph inputs model nat)

def report (guard : Flat (ULift Bool)) : List Task × Bool × Bool × Flat Nat :=
  letI : DecidableEq (sortValue model.value nat) := inferInstanceAs (DecidableEq Nat)
  let result := run model (graph .onFalse) (inputs guard)
  (result.visits, decide (slotIndex .first ∈ result.state.1), decide (slotIndex .second ∈ result.state.1),
    result.state.2.2)

/-- Run the producer equation with all but one vertex's fact already
available and the true occurrence marked. Return the newly queued jobs. -/
def pendingAfterLearning (vertex : Nat) : List Task :=
  letI : DecidableEq (sortValue model.value nat) := inferInstanceAs (DecidableEq Nat)
  let g := graph .onFalse
  let entry := inputs (.constant ⟨true⟩)
  let state := (run model g entry).state
  let prior : ProducerFacts model.value (RVSDG.extend [] SCCP.Example.Sigs) :=
    fun i => if i.val = vertex then ⊥ else state.2.1 i
  (step model g entry .producers (state.1, prior, state.2.2) []).2

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist.Example
