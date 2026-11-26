module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {summary : MemberSummary V S} {imports : Ports (Ty V S)}

/-- At every finite observation depth, the actual singleton-member jobs
match. The existing finite derivation lemmas apply to this certificate. -/
theorem Singleton.calls_prefix (family : Singleton Op summary imports) (actions : Actions m σ) (demand : Demand)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (family.invocation importedL argsL), store⟩
      ⟨Continuation.start (family.invocation importedR argsR), store⟩ :=
  Proofs.singleton_calls family actions demand importedL importedR argsL argsR store readyL readyR agree

/-- The linked runner matches exact finite endpoints at each budget. At a
block the additional depth is arbitrary for observing both saved stacks
after a common resumption. The suspension case preserves absence of a
finite endpoint when quantified over all budgets. -/
theorem Singleton.linked_prefixes_agree (family : Singleton Op summary imports)
    (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∃ left right,
      family.run actions fuel unitId importedL argsL store = .ok left ∧
      family.run actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  Proofs.singleton_linked family actions demand fuel after unitId importedL importedR argsL argsR store
    readyL readyR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
