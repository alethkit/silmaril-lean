module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)
open Continuation.Partial (Config)
open Continuation.Partial.Executable (Actions observe runFor)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {entry results : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- The executable summary computes the least shared may solution at entry. -/
theorem Code.mem_liveIn_iff (code : Code Op entry [] sigs results) (demand : Demand) (a : Address) :
    a ∈ code.liveIn demand ↔ a ∈ (code.liveness demand).mayOut 0 :=
  Proofs.mem_liveIn_iff code demand a

/-- A matched execution, including any matched resumption, settles at
a common budget and exposes related exact observations. -/
theorem Matches.settles {actions : Actions m σ} {demand : Demand} {left right : Config m σ results}
    (checked : Matches actions demand left right) :
    ∃ fuel, EndpointsAgree actions demand
      (observe actions (runFor actions fuel left)) (observe actions (runFor actions fuel right)) :=
  Proofs.settles checked

/-- Compare actual calls with the same checked body. Live entry agreement
is needed only on the combined tuple of captures and formal arguments. -/
theorem Code.matches_calls {fn : Function V S} {context : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) [] sigs fn.results)
    (actions : Actions m σ) (demand : Demand) (fL fR : m.Val fn.port)
    (capsL capsR : Tuple m.Val context) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closureL : fL = .closure capsL code.term.toGraph)
    (closureR : fR = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    Matches actions demand
      ⟨Continuation.start (.call fL argsL), store⟩
      ⟨Continuation.start (.call fR argsR), store⟩ :=
  Proofs.matches_calls code actions demand fL fR capsL capsR argsL argsR store closureL closureR
    resolvedL resolvedR agree

/-- After successful link at a common store, dispatch the actual callable
export. Both runs reach related returns or typed blocks, and any common
hypothetical primitive result and store resumes related saved contexts. -/
theorem Code.linked_runs_agree {fn : Function V S} {context : Ports (Ty V S)}
    {imports exports : Ports (Ty V S)} {moduleSigs : List (Ports (Ty V S))}
    (code : Code Op (context ++ fn.args) [] sigs fn.results)
    (actions : Actions m σ) (demand : Demand) (graph : Omega Op imports exports moduleSigs)
    (unitId : Nat) (port : Port exports fn.port)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val fn.args) (initial : σ)
    {exportsL exportsR : Tuple m.Val exports} {middle : σ}
    {capsL capsR : Tuple m.Val context}
    (linkedL : Executable.link actions unitId graph inputsL initial = .linked exportsL middle)
    (linkedR : Executable.link actions unitId graph inputsR initial = .linked exportsR middle)
    (closureL : exportsL.get port = .closure capsL code.term.toGraph)
    (closureR : exportsR.get port = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∃ fuel observedL observedR,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok observedL ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok observedR ∧
      EndpointsAgree actions demand observedL observedR :=
  Proofs.linked_runs_agree code actions demand graph unitId port inputsL inputsR argsL argsR initial
    linkedL linkedR closureL closureR resolvedL resolvedR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
