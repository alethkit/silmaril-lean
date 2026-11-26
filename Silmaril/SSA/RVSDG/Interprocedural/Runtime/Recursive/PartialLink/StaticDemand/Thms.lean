module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Prefix

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand)
open Continuation.Partial (Config Eval Site)
open Continuation.Partial.Executable (Actions Observation observe runFor)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {entry results : Ports (Ty V S)} {sigs : List (Ports (Ty V S))} {loops : Bool}
variable {member : Option (MemberSummary V S)}

/-- The executable summary computes the least shared may solution at entry. -/
theorem Code.mem_liveIn_iff (code : Code Op entry [] sigs results loops member) (demand : Demand) (a : Address) :
    a ∈ code.liveIn demand ↔ a ∈ (code.liveness demand).mayOut 0 :=
  Proofs.mem_liveIn_iff code demand a

/-- The linked body's feedback transfer uses the native finite least fixed point. -/
theorem Code.feedbackLive_isLeast {carried : Ports (Ty V S)}
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member) (exit : Demand) :
    IsLeast {live | NestedTheta.Liveness.Feedback.step exit (fun demand => (body.plan demand).live) live = live}
      (body.feedbackLive exit) :=
  Proofs.feedback_isLeast body exit

/-- Inspect the actual runner after a finite prefix. The independent
remaining depth can be used to inspect subsequent hypothetical resumptions. -/
theorem PrefixMatches.observes {actions : Actions m σ} {demand : Demand} {left right : Config m σ results}
    (fuel after : Nat) (checked : PrefixMatches actions demand (fuel + after + 1) left right) :
    PrefixObservationsAgree actions demand after
      (observe actions (runFor actions fuel left)) (observe actions (runFor actions fuel right)) :=
  Proofs.prefix_observes fuel after checked

/-- At a matched budget, either both runs still have work or both have a
finite endpoint. Quantifying over budgets preserves absence of an endpoint. -/
theorem PrefixObservationsAgree.suspended_iff {actions : Actions m σ} {demand : Demand} {after : Nat}
    {left right : Observation m σ results} (checked : PrefixObservationsAgree actions demand after left right) :
    (∃ c, left = .suspended c) ↔ ∃ c, right = .suspended c := by
  cases checked <;> simp

/-- Every finite evaluation returning on one side matches a return with
the same store and demanded results. -/
theorem PrefixMatches.finite_return {actions : Actions m σ} {demand : Demand}
    {jobL jobR : Job m results} {initial stopped : σ} {value : Tuple m.Val results}
    (matched : ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start jobL, initial⟩ ⟨Continuation.start jobR, initial⟩)
    (evaluated : Eval actions.toPrimitives jobL initial (.returned value stopped)) :
    ∃ other, Eval actions.toPrimitives jobR initial (.returned other stopped) ∧ demand.Agrees value other :=
  Proofs.finite_return matched evaluated

/-- Every finite blocked derivation matches the exact typed attempt and store.
The pending stacks have matching finite observations after a common resumption. -/
theorem PrefixMatches.finite_block {actions : Actions m σ} {demand : Demand}
    {jobL jobR : Job m results} {initial stopped : σ} {site : Site m}
    {pendingL : Continuation.Descent.Pending m site.outs results}
    (matched : ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start jobL, initial⟩ ⟨Continuation.start jobR, initial⟩)
    (evaluated : Eval actions.toPrimitives jobL initial (.blocked site pendingL stopped)) :
    ∃ pendingR, Eval actions.toPrimitives jobR initial (.blocked site pendingR stopped) ∧
      ∀ depth value store, PrefixMatches actions demand depth
        ⟨.returned value (pendingL.push .halt), store⟩ ⟨.returned value (pendingR.push .halt), store⟩ :=
  Proofs.finite_block matched evaluated

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

/-- Compare the finite prefixes of actual calls, including feedback. The
same certificate transports finite partial derivations via `finite_return`
and `finite_block`. -/
theorem Code.calls_prefix {fn : Function V S} {context : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) [] sigs fn.results loops)
    (actions : Actions m σ) (demand : Demand) (fL fR : m.Val fn.port)
    (capsL capsR : Tuple m.Val context) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closureL : fL = .closure capsL code.term.toGraph)
    (closureR : fR = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (.call fL argsL), store⟩
      ⟨Continuation.start (.call fR argsR), store⟩ :=
  Proofs.calls_prefix code actions demand fL fR capsL capsR argsL argsR store closureL closureR
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

/-- After successful linkage, every finite budget either leaves both
invocations live or matches their finite endpoints. The remaining observation
depth is arbitrary, including for a restart from a hypothetically resumed block. -/
theorem Code.linked_prefixes_agree {fn : Function V S} {context : Ports (Ty V S)}
    {imports exports : Ports (Ty V S)} {moduleSigs : List (Ports (Ty V S))}
    (code : Code Op (context ++ fn.args) [] sigs fn.results loops)
    (actions : Actions m σ) (demand : Demand) (fuel after : Nat) (graph : Omega Op imports exports moduleSigs)
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
    ∃ observedL observedR,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok observedL ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok observedR ∧
      PrefixObservationsAgree actions demand after observedL observedR :=
  Proofs.linked_prefixes_agree code actions demand fuel after graph unitId port inputsL inputsR argsL argsR initial
    linkedL linkedR closureL closureR resolvedL resolvedR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
