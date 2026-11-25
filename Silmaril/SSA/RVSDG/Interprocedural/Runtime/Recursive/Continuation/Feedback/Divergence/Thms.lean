module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Decomposition

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {carried final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {parent : Stack m carried final} {input : Tuple m.Val carried}
variable {micro : Nat → State m final}

/-- Extract the restart checkpoints or the final nonreturning body from the
given infinite machine execution. The converse rules out a θ exit anywhere
in an execution with either decomposition. -/
theorem stays_iff_decomposes (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (initial : micro 0 = restart body parent input) :
    StaysInLoop body parent micro ↔ Decomposes body parent input micro :=
  ⟨Proofs.decompose steps initial, Proofs.stays_of_decomposes steps⟩

/-- The same extraction for an execution already evaluating the fresh body,
with the entry step prepended to use the restart convention. -/
theorem body_decomposes (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (initial : micro 0 = .eval (.region body input (PUnit.unit : Locals m.Val [])) (.loop body parent))
    (stays : StaysInLoop body parent micro) :
    Decomposes body parent input (withEntry body parent input micro) :=
  Proofs.body_decomposes steps initial stays

/-- Each interval of the finite checkpoint prefix is justified by an
independent finite body return and its feedback selector. -/
theorem Interval.iteration {first last : Checkpoint m carried}
    (edge : Interval body parent micro first last) (steps : ∀ i, Step (micro i) (micro (i + 1))) :
    Iteration body first.2 last.2 :=
  iteration_iff_segment.mpr
    (segment_of_positions steps edge.atStart edge.atNext edge.later edge.bodyReturn edge.inside)

/-- The alternatives are disjoint on the supplied microstep stream. -/
theorem no_bodyForever_of_restarts {inputs : Nat → Tuple m.Val carried} {indices : Nat → Nat}
    (trace : RestartTrace body parent inputs micro indices) (point : Checkpoint m carried) :
    ¬ BodyForever body parent micro point :=
  Proofs.no_bodyForever_of_restarts trace point

/-- The actual nonreturning suffix starts with fresh locals and takes
only steps delimited by the saved frame. -/
theorem BodyForever.bodySuffix {point : Checkpoint m carried}
    (forever : BodyForever body parent micro point)
    (steps : ∀ i, Step (micro i) (micro (i + 1))) :
    micro (point.1 + 1) =
        .eval (.region body point.2 (PUnit.unit : Locals m.Val [])) (.loop body parent) ∧
      ∀ i, InsideStep (.loop body parent) (micro (point.1 + i + 1)) (micro (point.1 + i + 1 + 1)) :=
  ⟨step_deterministic (a := restart body parent point.2) (forever.1 ▸ steps point.1) rfl,
    fun i => ⟨steps (point.1 + i + 1), forever.2 _ (by omega)⟩⟩

/-- Concatenate any finite sequence of completed feedback iterations
and an infinite delimited body execution under the same saved frame. -/
theorem trace_of_iterations_then_body {last : Tuple m.Val carried}
    (iterations : Relation.ReflTransGen (Iteration body) input last)
    (bodyTrace : InfiniteTrace (InsideStep (.loop body parent))
      (.eval (.region body last (PUnit.unit : Locals m.Val [])) (.loop body parent))) :
    ∃ micro : Nat → State m final, micro 0 = restart body parent input ∧
      (∀ i, Step (micro i) (micro (i + 1))) ∧ StaysInLoop body parent micro :=
  Proofs.trace_of_iterations_then_body iterations bodyTrace

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence
