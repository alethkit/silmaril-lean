module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}

/-- The actual linked export dispatches the chosen member with its typed arguments. -/
theorem Family.starts (family : Family Op table imports) (i : Fin table.members.length)
    (actions : Actions m σ) (unitId : Nat)
    (imported : Tuple m.Val imports) (args : Tuple m.Val (table.at i).fn.args) (store : σ) :
    Executable.start actions unitId (family.graph i) imported .head args store =
      .ok ⟨Continuation.start (family.invocation i imported args), store⟩ :=
  Proofs.family_starts family i actions unitId imported args store

/-- Actual calls to any admitted member match at every finite observation
depth. The existing finite return and blocked derivation theorems consume
this certificate. -/
theorem Family.calls_prefix (family : Family Op table imports) (i : Fin table.members.length)
    (actions : Actions m σ) (demand : Demand)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val (table.at i).fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs i demand importedL importedR argsL argsR) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (family.invocation i importedL argsL), store⟩
      ⟨Continuation.start (family.invocation i importedR argsR), store⟩ :=
  Proofs.family_calls family i actions demand importedL importedR argsL argsR store readyL readyR agree

/-- The actual linked runner preserves demanded returns, exact stores,
typed blocks with matching resumption observations, and suspension at the
same finite budgets. -/
theorem Family.linked_prefixes_agree (family : Family Op table imports) (i : Fin table.members.length)
    (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val (table.at i).fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs i demand importedL importedR argsL argsR) :
    ∃ left right,
      family.run i actions fuel unitId importedL argsL store = .ok left ∧
      family.run i actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  Proofs.family_linked family i actions demand fuel after unitId importedL importedR argsL argsR store
    readyL readyR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
