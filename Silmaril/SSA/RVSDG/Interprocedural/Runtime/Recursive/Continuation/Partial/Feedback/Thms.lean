module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Replay

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback

open Descent (Pending)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {primitives : Primitives m σ} {carried ports final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {input next : Tuple m.Val carried × σ}
variable {job : Job m ports} {store : σ}

/-- The actual nonempty microstep segment preserves the parent frame and
restarts with the exact next tuple and store. -/
theorem Iteration.steps (ran : Iteration primitives body input next) (parent : Stack m carried final) :
    TransGen (Step primitives)
      (Restart.config ⟨carried, sigs, body, input⟩ parent)
      (Restart.config ⟨carried, sigs, body, next⟩ parent) :=
  Proofs.iteration_steps ran parent

theorem Run.infinite (ran : Run primitives body input) (parent : Stack m carried final) :
    InfiniteTrace (Step primitives) (Restart.config ⟨carried, sigs, body, input⟩ parent) :=
  Proofs.run_infinite ran parent

/-- Replay a finite route to the selected θ, retaining every live frame. -/
theorem Reaches.steps {target : Restart m σ} {pending : Pending m target.carried ports}
    (reached : Reaches primitives job store target pending) (frame : Stack m ports final) :
    ReflTransGen (Step primitives) ⟨.eval job frame, store⟩ (target.config (pending.push frame)) :=
  Proofs.reaches_steps reached frame

/-- A certificate from a linked invocation yields an infinite sequence of
actual partial-machine steps after replaying its finite reaching work. -/
theorem Productive.infinite (productive : Productive primitives job store) (frame : Stack m ports final) :
    InfiniteTrace (Step primitives) ⟨.eval job frame, store⟩ := by
  obtain ⟨_, pending, reached, ran⟩ := productive
  exact InfiniteTrace.of_steps (reached.steps frame) (ran.infinite (pending.push frame))

/-- Determinism makes a productive certificate incompatible with reaching
a finite selected block from the same initial configuration. -/
theorem Productive.no_block (productive : Productive primitives job store) (frame : Stack m ports final)
    {target : Config m σ final} (path : ReflTransGen (Step primitives) ⟨.eval job frame, store⟩ target) :
    ¬ target.Blocked primitives :=
  fun blocked => no_infinite_of_reaches_blocked path blocked (productive.infinite frame)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback
