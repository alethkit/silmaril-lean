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

/-- The nonreturning suffix takes only steps delimited by the saved frame. -/
theorem BodyForever.insideSteps {point : Checkpoint m carried}
    (forever : BodyForever body parent micro point)
    (steps : ∀ i, Step (micro i) (micro (i + 1))) :
    ∀ i, InsideStep (.loop body parent) (micro (point.1 + i + 1)) (micro (point.1 + i + 1 + 1)) :=
  fun i => ⟨steps (point.1 + i + 1), forever.2 _ (by omega)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence
