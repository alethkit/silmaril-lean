module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Replay
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Reflection

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent

open Descent (Pending stackDepth)
open Relation (TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {primitives : Primitives m σ} {ports final : Ports (Ty V S)}
variable {job : Job m ports} {store : σ} {next : Entry m σ} {pending : Pending m next.call.results ports}

/-- Replay a successful prefix up to the actual selected call, before
opening its body. The endpoint retains the exact store and live stack. -/
theorem Prefix.steps (reached : Prefix primitives job store next pending) (stack : Stack m ports final) :
    TransGen (Step primitives) ⟨.eval job stack, store⟩ (next.config (pending.push stack)) :=
  Proofs.prefix_steps reached stack

theorem entry_steps {entry : Entry m σ} {pending : Pending m next.call.results entry.call.results}
    (reached : Prefix primitives entry.call.openBody entry.store next pending)
    (stack : Stack m entry.call.results final) :
    TransGen (Step primitives) (entry.config stack) (next.config (pending.push stack)) :=
  Proofs.entry_steps reached stack

/-- Every selected next activation adds a pending typed frame. -/
theorem Run.stack_grows (run : Run primitives) (base : Stack m (run.entry 0).call.results final) (n : Nat) :
    stackDepth (run.stackAt base n) < stackDepth (run.stackAt base (n + 1)) :=
  Proofs.stack_grows run base n

/-- One actual microstep stream visits every specified call configuration
in order, with its full arguments, store and exact growing stack. -/
theorem Run.checkpoints (run : Run primitives) (base : Stack m (run.entry 0).call.results final) :
    ∃ micro positions, Checkpoints run base micro positions :=
  Proofs.checkpoints run base

theorem Run.infinite (run : Run primitives) (base : Stack m (run.entry 0).call.results final) :
    InfiniteTrace (Step primitives) ((run.entry 0).config base) := by
  obtain ⟨micro, _, trace⟩ := run.checkpoints base
  exact ⟨micro, by simpa only [trace.first, Run.stackAt] using trace.atEntry 0, trace.steps⟩

/-- Reflect a finite interval from a live caller to its selected deeper
call. Every earlier call entry in the interval must return to its own
frame before the endpoint. Completed θ feedback may precede the selected
application. The resulting prefix uses both observed stores and
reconstructs the exact stack at the selected call. -/
theorem entry_of_interval {micro : Nat → Config m σ final} {begin finish : Nat}
    (steps : ∀ i, begin ≤ i → i < finish → Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {stack : Stack m caller.call.results final} {nextStack : Stack m next.call.results final}
    (atCaller : micro begin = caller.config stack) (atCallee : micro finish = next.config nextStack)
    (rising : begin < finish)
    (live : Descent.BeforeReturn (fun i => (micro i).control) (begin + 1) finish stack)
    (earlier : Descent.EarlierCallsReturn (fun i => (micro i).control) (begin + 1) finish) :
    ∃ pending, Prefix primitives caller.call.openBody caller.store next pending ∧ pending.push stack = nextStack :=
  Proofs.entry_of_interval steps atCaller atCallee rising live earlier

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent
