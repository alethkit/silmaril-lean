module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Runner

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {actions : Actions m σ} {source target : Config m σ final}

theorem Actions.toPrimitives_liftTotal :
    (Actions.liftTotal m σ).toPrimitives = Primitives.liftTotal m σ := rfl

/-- The executable successor denotes exactly the partial successor. -/
theorem next_eq (actions : Actions m σ) (source : Config m σ final) :
    source.next actions.toPrimitives = _root_.Part.ofOption (next? actions source) :=
  Proofs.next_eq actions source

theorem step_iff : Step actions.toPrimitives source target ↔ next? actions source = some target :=
  Proofs.step_iff

/-- Splitting a budget gives the same live or terminal configuration as
running it in one segment. -/
theorem runFor_add (actions : Actions m σ) (first more : Nat) (source : Config m σ final) :
    runFor actions (first + more) source = runFor actions more (runFor actions first source) :=
  Proofs.runFor_add actions first more source

theorem runFor_reachable (actions : Actions m σ) (fuel : Nat) (source : Config m σ final) :
    ReflTransGen (Step actions.toPrimitives) source (runFor actions fuel source) :=
  Proofs.runFor_reachable actions fuel source

/-- Every finite prefix, including one inside an active recursive call
or θ body, is obtained at some budget. -/
theorem reachable_iff :
    ReflTransGen (Step actions.toPrimitives) source target ↔ ∃ fuel, runFor actions fuel source = target :=
  Proofs.reachable_iff

theorem observe_returned {values : Tuple m.Val final} {store : σ} :
    observe actions source = .returned values store ↔ source = ⟨.returned values .halt, store⟩ :=
  Proofs.observe_returned

theorem observe_blocked {active : ActivePrimitive m final} {store : σ} :
    observe actions source = .blocked active store ↔
      selectedPrimitive source.control = some active ∧ source.store = store ∧
        (actions.toPrimitives.step active.site.opcode active.site.input).run source.store = _root_.Part.none :=
  Proofs.observe_blocked

theorem observe_suspended :
    observe actions source = .suspended source ↔ ∃ target, Step actions.toPrimitives source target :=
  Proofs.observe_suspended

theorem returns_iff_run {job : Job m final} {initial store : σ} {values : Tuple m.Val final} :
    Eval actions.toPrimitives job initial (.returned values store) ↔
      ∃ fuel, run actions fuel job initial = .returned values store :=
  Proofs.returns_iff_run

/-- The executable block reports the same site, attempted store, and live
stack as the independent finite blocked judgment. -/
theorem blocks_iff_run {job : Job m final} {initial store : σ} {active : ActivePrimitive m final} :
    (∃ pending, Eval actions.toPrimitives job initial (.blocked active.site pending store) ∧
      active.stack = pending.push .halt) ↔
      ∃ fuel, run actions fuel job initial = .blocked active store :=
  Proofs.blocks_iff_run

/-- Divergence is equivalent to observing a live configuration at every
budget. The reverse constructs a productive step at each successive budget. -/
theorem infinite_iff_all_suspended :
    InfiniteTrace (Step actions.toPrimitives) source ↔
      ∀ fuel, observe actions (runFor actions fuel source) = .suspended (runFor actions fuel source) :=
  Proofs.infinite_iff_all_suspended

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable
