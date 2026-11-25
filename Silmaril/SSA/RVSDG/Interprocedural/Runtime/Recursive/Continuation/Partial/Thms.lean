module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Machine
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Evaluation

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

/-- A finite path to a blocked primitive rules out an infinite
control run from the same initial configuration. -/
theorem no_infinite_of_reaches_blocked
    (path : Relation.ReflTransGen (Step primitives) source target)
    (blocked : target.Blocked primitives) : ¬ InfiniteTrace (Step primitives) source :=
  Proofs.no_infinite_of_reaches_blocked path blocked

theorem no_blocked_liftTotal : ¬ source.Blocked (Primitives.liftTotal m σ) :=
  Proofs.no_blocked_liftTotal source

/-- The canonical lift of the existing total interpretation preserves
every control transition and leaves the separate store unchanged. -/
theorem step_liftTotal_iff :
    Step (Primitives.liftTotal m σ) source target ↔
      Continuation.Step source.control target.control ∧ source.store = target.store :=
  Proofs.step_liftTotal

variable {job : Job m ports} {store : σ} {outcome : Outcome m σ ports}

/-- Soundness of both finite outcomes under any enclosing typed stack. -/
theorem Eval.steps (evaluation : Eval primitives job store outcome) (frame : Stack m ports final) :
    Relation.ReflTransGen (Step primitives) ⟨.eval job frame, store⟩ (outcome.atStack frame) :=
  Proofs.eval_steps evaluation frame

/-- A finite blocking derivation reaches its first undefined primitive
with the exact store and pending stack. No step leaves that endpoint. -/
theorem Eval.blocks {site : Site m} {pending : Descent.Pending m site.outs ports} {stopped : σ}
    (evaluation : Eval primitives job store (.blocked site pending stopped)) (frame : Stack m ports final) :
    (Config.mk (.eval site.job (pending.push frame)) stopped).Blocked primitives :=
  Proofs.eval_blocked evaluation frame

/-- The lifted total model has exactly the old finite returns and keeps
the extra store unchanged. -/
theorem eval_liftTotal_iff {value : Tuple m.Val ports} {finalStore : σ} :
    Eval (Primitives.liftTotal m σ) job store (.returned value finalStore) ↔
      Recursive.Returns m job value ∧ store = finalStore :=
  Proofs.eval_liftTotal

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
