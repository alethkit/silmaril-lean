module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Machine

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {source target : Config m σ final}

theorem Config.Blocked.next_none (stopped : source.Blocked primitives) :
    source.next primitives = _root_.Part.none :=
  Proofs.blocked_next stopped

theorem Config.Blocked.result_none (stopped : source.Blocked primitives) : source.result = none :=
  Proofs.blocked_result stopped

theorem Config.Blocked.no_step (stopped : source.Blocked primitives) : ¬ Step primitives source target := by
  intro stepped
  exact _root_.Part.notMem_none _ (stopped.next_none ▸ (show target ∈ source.next primitives from stepped))

theorem Config.Blocked.no_infinite (stopped : source.Blocked primitives) :
    ¬ InfiniteTrace (Step primitives) source :=
  fun trace => let ⟨_, stepped, _⟩ := trace.unfold; stopped.no_step stepped

/-- The canonical lift of the existing total interpretation preserves
every control transition and leaves the separate store unchanged. -/
theorem step_liftTotal_iff :
    Step (Primitives.liftTotal m σ) source target ↔
      Continuation.Step source.control target.control ∧ source.store = target.store :=
  Proofs.step_liftTotal

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
