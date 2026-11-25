module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Adequacy

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {args outs : Ports (Ty V S)}
variable {job : Job m outs} {output : Tuple m.Val outs}

theorem step_deterministic {a b c : State m outs} (left : Step a b) (right : Step a c) : b = c :=
  Option.some.inj (left.symm.trans right)

theorem runFor_reachable (fuel : Nat) (state : State m outs) :
    Relation.ReflTransGen Step state (State.runFor fuel state) :=
  Proofs.runFor_reachable fuel state

theorem completes_runFor {state : State m outs} {fuel : Nat}
    (result : (State.runFor fuel state).result = some output) : Completes state output :=
  Proofs.completes_runFor result

/-- A completed machine run derives the full returned tuple in the
independent finite runtime judgment. -/
theorem completes_sound (completed : Completes (start job) output) : Returns m job output :=
  Proofs.completes_sound completed

/-- Every finite derivation is realized by a completed machine trace. -/
theorem completes_of_returns (returned : Returns m job output) : Completes (start job) output :=
  Proofs.completes_of_returns returned

theorem completes_iff_returns : Completes (start job) output ↔ Returns m job output :=
  ⟨completes_sound, completes_of_returns⟩

/-- The previous scoped completion statement as a corollary of full finite adequacy. -/
theorem returns_or_unsupported (returned : Returns m job output) :
    Completes (start job) output ∨
      ∃ state, Relation.ReflTransGen Step (start job) state ∧ state.Unsupported :=
  .inl (completes_of_returns returned)

/-- A machine state can stop only at a completed return. This is a
one-step progress statement, independent of finite termination. -/
theorem no_unsupported (state : State m outs) : ¬ state.Unsupported :=
  Proofs.no_unsupported state

theorem admitted_all (state : State m outs) : Admitted state :=
  fun reached _ => no_unsupported reached

theorem admitted_of_completes {state : State m outs} (_completed : Completes state output) :
    Admitted state :=
  admitted_all state

theorem completes_iff :
    Completes (start job) output ↔ Returns m job output ∧ Admitted (start job) :=
  ⟨fun completed => ⟨completes_sound completed, admitted_of_completes completed⟩,
    fun ⟨returned, _⟩ => completes_of_returns returned⟩

/-- For a supported call, completion agrees with every finite return of the
real interpreter, including all value and state ports. -/
theorem completes_call_iff_invoke (callee : m.Val (.value (.function args outs)))
    (input : Tuple m.Val args) (admitted : Admitted (start (.call callee input))) :
    Completes (start (.call callee input)) output ↔
      ∃ loops depth, invoke m loops depth callee input = some output :=
  (completes_iff.trans (and_iff_left admitted)).trans (Recursive.call_iff m callee input output)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation
