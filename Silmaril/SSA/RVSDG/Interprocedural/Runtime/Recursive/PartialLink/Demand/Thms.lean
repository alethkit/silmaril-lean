module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {caller callee : Function V S}

/-- The executable callee summary is the least may solution of the shared
equations at the demand passed through the caller's result wires. -/
theorem DirectCall.mem_calleeLiveIn_iff (call : DirectCall Op imports caller callee)
    (demand : Demand) (a : Address) :
    a ∈ call.calleeLiveIn demand ↔ a ∈ (call.calleeLiveness demand).mayOut 0 :=
  Proofs.liveIn_iff call demand a

/-- Ten microsteps suffice for either endpoint of this admitted module.
Live-input agreement matches demanded returns and exact stores, or the
same blocked site, operands and store with behaviorally related stacks. -/
theorem DirectCall.run_agrees (call : DirectCall Op imports caller callee)
    (actions : Actions m σ) (unitId more : Nat) (demand : Demand)
    (importsL importsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val caller.args) (store : σ)
    (agree : call.AgreesOnInputs demand importsL importsR argsL argsR) :
    ∃ observationL observationR,
      call.run actions (10 + more) unitId importsL argsL store = .ok observationL ∧
      call.run actions (10 + more) unitId importsR argsR store = .ok observationR ∧
      ObservationsAgree actions demand observationL observationR :=
  Proofs.run_agrees call actions unitId more demand importsL importsR argsL argsR store agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand
