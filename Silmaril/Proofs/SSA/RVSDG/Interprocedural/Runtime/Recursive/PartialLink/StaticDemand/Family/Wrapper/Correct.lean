module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Wrapper.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Correct
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness (Demand)
open Continuation.Partial (Config)
open Continuation.Partial.Executable (Actions next?)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {fn : Function V S}
variable {family : Family Op table imports}

theorem lambda_calls (family : Family Op table imports) {context : Ports (Ty V S)}
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
      ⟨Continuation.start (.call (.closure capsR code.term.toGraph) argsR), store⟩ := by
  intro depth
  cases depth with
  | zero => exact .cut _ _
  | succ n =>
    have enter (caps : Tuple m.Val context) (args : Tuple m.Val fn.args) :
        next? actions ⟨Continuation.start (.call (.closure caps code.term.toGraph) args), store⟩ =
          some (⟨.eval (.region code.term (prependContext args caps) PUnit.unit) .halt, store⟩ :
            Config m σ fn.results) := by
      change some (⟨.eval (.region code.term.toGraph.toTerm (prependContext args caps) PUnit.unit) .halt, store⟩ :
        Config m σ fn.results) = _
      rw [NestedTheta.Term.toTerm_toGraph]
    apply PrefixMatches.step (enter capsL argsL) (enter capsR argsR)
    apply region actions demand code (family.guard groupL) (family.guard groupR) (some n) (by simp)
      (family_dispatch family actions demand groupL groupR closedL closedR n) demand _ _ PUnit.unit PUnit.unit
      .halt .halt store resolvedL resolvedR
    · intro ty source needed
      cases source with
      | output i _ => exact i.elim0
      | arg p => exact agree p (List.mem_eraseDups.2 needed)
    · intro outL outR middle observed _ _
      cases n with
      | zero => exact .cut _ _
      | succ n => exact .returned observed

variable (wrapper : Family.Wrapper family fn)

theorem wrapper_starts (actions : Actions m σ) (unitId : Nat)
    (imported : Tuple m.Val imports) (args : Tuple m.Val fn.args) (store : σ) :
    Executable.start actions unitId wrapper.graph imported .head args store =
      .ok ⟨Continuation.start (wrapper.invocation imported args), store⟩ := rfl

theorem wrapper_linked (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (readyL : wrapper.Ready importedL argsL) (readyR : wrapper.Ready importedR argsR)
    (agree : wrapper.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∃ left right,
      wrapper.run actions fuel unitId importedL argsL store = .ok left ∧
      wrapper.run actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right := by
  have matched := prefix_observes fuel after
    (lambda_calls family wrapper.body actions demand (family.captures.read importedL PUnit.unit)
      (family.captures.read importedR PUnit.unit)
      (wrapper.capturedAt importedL) (wrapper.capturedAt importedR) argsL argsR store
      readyL.1 readyR.1 readyL.2 readyR.2 agree _)
  refine ⟨_, _, ?_, ?_, matched⟩
  · simp only [Family.Wrapper.run, Executable.run, wrapper_starts]
    rfl
  · simp only [Family.Wrapper.run, Executable.run, wrapper_starts]
    rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
