module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Wrapper.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Wrapper.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {fn : Function V S}
variable {family : Family Op table imports}

/-- Calls of actual λ closures over a checked φ group match at every finite
observation depth. A client with another link layout can use this theorem
after identifying the linked closure and post-link store. -/
theorem Family.lambda_calls_prefix (family : Family Op table imports) {context : Ports (Ty V S)}
    {sigs : List (Ports (Ty V S))}
    (code : Code Op (context ++ fn.args) [] sigs fn.results true (some table))
    (actions : Actions m σ) (demand : Demand)
    (groupL groupR : Tuple m.Val family.context) (capsL capsR : Tuple m.Val context)
    (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closedL : family.Ready groupL) (closedR : family.Ready groupR)
    (resolvedL : code.ResolvedWith (family.guard groupL) (prependContext argsL capsL))
    (resolvedR : code.ResolvedWith (family.guard groupR) (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (.call (.closure capsL code.term.toGraph) argsL), store⟩
      ⟨Continuation.start (.call (.closure capsR code.term.toGraph) argsR), store⟩ :=
  Proofs.lambda_calls family code actions demand groupL groupR capsL capsR argsL argsR store
    closedL closedR resolvedL resolvedR agree

variable (wrapper : Family.Wrapper family fn)

/-- The ordinary origin list is the least shared may solution at entry. -/
theorem Family.Wrapper.mem_liveIn_iff (demand : Demand) (origin : Address) :
    origin ∈ wrapper.liveIn demand ↔ origin ∈ (wrapper.body.liveness demand).mayOut 0 :=
  wrapper.body.mem_liveIn_iff demand origin

/-- The runner starts the λ export with its actual linked φ capture. -/
theorem Family.Wrapper.starts (actions : Actions m σ) (unitId : Nat)
    (imported : Tuple m.Val imports) (args : Tuple m.Val fn.args) (store : σ) :
    Executable.start actions unitId wrapper.graph imported .head args store =
      .ok ⟨Continuation.start (wrapper.invocation imported args), store⟩ :=
  Proofs.wrapper_starts wrapper actions unitId imported args store

/-- Agreement on the computed inputs preserves demanded returns, exact
stores, typed blocked attempts, and observations of the saved suffixes
after a common primitive result and resumption store. -/
theorem Family.Wrapper.linked_prefixes_agree (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (readyL : wrapper.Ready importedL argsL) (readyR : wrapper.Ready importedR argsR)
    (agree : wrapper.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∃ left right,
      wrapper.run actions fuel unitId importedL argsL store = .ok left ∧
      wrapper.run actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  Proofs.wrapper_linked wrapper actions demand fuel after unitId importedL importedR argsL argsR
    store readyL readyR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
