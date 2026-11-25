module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Proofs

open CallDescent (Entry)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ}

private theorem route_infinite {caller : Entry m σ} {stack : Stack m caller.call.results final}
    (route : FeedbackRoute primitives caller stack) : InfiniteTrace (Step primitives) (caller.config stack) := by
  induction route with
  | @restart caller stack target pending reaches productive =>
    have entered : Step primitives (caller.config stack) ⟨.eval caller.call.openBody stack, caller.store⟩ :=
      .of_next_some rfl
    exact InfiniteTrace.of_steps ((reaches.steps stack).head entered)
      (productive.infinite (pending.push stack))
  | call reaches _ ih =>
    exact InfiniteTrace.of_steps (CallDescent.entry_steps reaches _).to_reflTransGen ih

theorem diverges_sound {entry : Entry m σ} (certificate : Diverges primitives entry) :
    InfiniteTrace (Step primitives) (entry.config .halt) := by
  rcases certificate with ⟨run, first⟩ | route
  · subst entry
    exact run.infinite .halt
  · exact route_infinite route

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Proofs
