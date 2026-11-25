module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Streams

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback

open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {carried ports final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {parent : Stack m carried final} {input next : Tuple m.Val carried}

/-- The first return to an enclosing frame agrees with the finite
runtime judgment for the active job. -/
theorem returns_iff_delimited (frame : Stack m ports final) {job : Job m ports}
    {value : Tuple m.Val ports} :
    Returns m job value ↔ ReflTransGen (InsideStep frame) (.eval job frame) (.returned value frame) :=
  Proofs.returns_iff_delimited frame

/-- A completed feedback iteration corresponds to a delimited body
run followed by the actual feedback edge. -/
theorem iteration_iff_segment : Iteration body input next ↔ Segment body parent input next :=
  Proofs.iteration_iff_segment

theorem segment_steps (segment : Segment body parent input next) :
    TransGen Step (restart body parent input) (restart body parent next) :=
  Proofs.segment_steps segment

/-- An activation with no finite body return supplies no feedback segment. -/
theorem no_segment_of_no_return
    (noReturn : ∀ value, ¬ Returns m (.region body input (PUnit.unit : Locals m.Val [])) value) :
    ¬ Segment body parent input next := by
  intro segment
  obtain ⟨_, returned, _⟩ := iteration_iff_segment.mpr segment
  exact noReturn _ returned

theorem restarts_of_segments (inputs : Nat → Tuple m.Val carried)
    (segments : ∀ n, Segment body parent (inputs n) (inputs (n + 1))) :
    ∃ micro indices, RestartTrace body parent inputs micro indices :=
  Proofs.restarts_of_segments inputs segments

theorem segments_of_restarts {inputs : Nat → Tuple m.Val carried} {micro : Nat → State m final}
    {indices : Nat → Nat} (trace : RestartTrace body parent inputs micro indices) :
    ∀ n, Segment body parent (inputs n) (inputs (n + 1)) :=
  Proofs.segments_of_restarts trace

/-- Match a supplied sequence of completed feedback activations at every
restart in a single productive continuation trace. In reverse, the
supplied restart and body-return checkpoints determine the iterations. -/
theorem iterations_iff_restarts (inputs : Nat → Tuple m.Val carried) :
    (∀ n, Iteration body (inputs n) (inputs (n + 1))) ↔
      ∃ micro indices, RestartTrace body parent inputs micro indices :=
  ⟨fun edges => restarts_of_segments inputs fun n => iteration_iff_segment.mp (edges n),
    fun ⟨_, _, trace⟩ n => iteration_iff_segment.mpr (segments_of_restarts trace n)⟩

theorem run_iff_restarts : Run body input ↔
    ∃ (inputs : Nat → Tuple m.Val carried) (micro : Nat → State m final) (indices : Nat → Nat),
      inputs 0 = input ∧ RestartTrace body parent inputs micro indices :=
  Proofs.run_iff_restarts

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback
