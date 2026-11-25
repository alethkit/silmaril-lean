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

/-- Every finite derivation yields a completed run or reaches unsupported
control in finitely many machine steps. -/
theorem returns_or_unsupported (returned : Returns m job output) :
    Completes (start job) output ∨
      ∃ state, Relation.ReflTransGen Step (start job) state ∧ state.Unsupported :=
  Proofs.returns_or_unsupported returned

/-- No execution from the same deterministic start can stop unsupported
when a completed run exists. -/
theorem admitted_of_completes {state : State m outs} (completed : Completes state output) :
    Admitted state :=
  Proofs.admitted_of_completes completed

theorem completes_iff :
    Completes (start job) output ↔ Returns m job output ∧ Admitted (start job) :=
  ⟨fun completed => ⟨completes_sound completed, admitted_of_completes completed⟩,
    fun ⟨returned, admitted⟩ => Proofs.completes_of_returns admitted returned⟩

/-- For a supported call, completion agrees with every finite return of the
real interpreter, including all value and state ports. -/
theorem completes_call_iff_invoke (callee : m.Val (.value (.function args outs)))
    (input : Tuple m.Val args) (admitted : Admitted (start (.call callee input))) :
    Completes (start (.call callee input)) output ↔
      ∃ loops depth, invoke m loops depth callee input = some output :=
  (completes_iff.trans (and_iff_left admitted)).trans (Recursive.call_iff m callee input output)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation
