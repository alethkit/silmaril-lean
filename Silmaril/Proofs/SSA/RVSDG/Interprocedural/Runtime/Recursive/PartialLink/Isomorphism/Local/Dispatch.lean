module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Evaluation
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Proofs

open Continuation.Partial (Primitives Eval Config Step)
open PartialLink.Invocation (Request start_linked start_error_iff)
open Isomorphism.Invocation (request)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {rename : Renaming}
variable {args outs params results : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}

theorem terminal_iff {source expected target : Config m σ results}
    (observed : TerminalPath primitives source expected) :
    TerminalPath primitives source target ↔ target = expected := by
  refine ⟨fun actual => ?_, fun equal => equal.symm ▸ observed⟩
  exact RightUnique.reach_final_eq (R := Step primitives) (fun _ _ _ a b => _root_.Part.mem_unique a b)
    actual.path observed.path actual.terminal observed.terminal

private theorem eval_terminal {job : Job m results} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ results}
    (evaluation : Eval primitives job store outcome) :
    TerminalPath primitives ⟨Continuation.start job, store⟩ (outcome.atStack .halt) := by
  refine ⟨evaluation.steps .halt, ?_⟩
  cases outcome with
  | returned =>
    intro _ stepped
    exact _root_.Part.notMem_none _ stepped
  | blocked => exact fun _ => (evaluation.blocks .halt).no_step

private theorem prepend_related {context : Ports (Ty V S)}
    {capturesL capturesR : Tuple m.Val context} {argsL argsR : Tuple m.Val params}
    (captures : TupleRelated m ids capturesL capturesR) (arguments : TupleRelated m ids argsL argsR) :
    TupleRelated m ids (prependContext argsL capturesL) (prependContext argsR capturesR) := by
  induction context with
  | nil => cases captures; exact arguments
  | cons _ _ ih => cases captures with | cons head tail => exact .cons head (ih tail)

private theorem open_lambda {context : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    (body : Graph Op (context ++ params) [] sigs results)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    Job.openClosure m (.closure captures (embed body.toTerm).toGraph) arguments =
      .region (embed body.toTerm) (prependContext arguments captures) PUnit.unit :=
  congrArg (fun term => Job.region (m := m) (past := []) term (prependContext arguments captures) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph (embed body.toTerm))

theorem calls (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ScheduledLambda m ids rename params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ) :
    CallPair primitives ids rename results
      ⟨Continuation.start (.call calleeL argsL), store⟩
      ⟨Continuation.start (.call calleeR argsR), store⟩ := by
  cases callees with
  | @closure context sigsL sigsR capturesL capturesR left right captures code =>
    obtain ⟨_, _, pair⟩ := graph_evaluate code respects (prepend_related captures arguments) store
    have machineL := open_lambda left capturesL argsL
    have machineR := open_lambda right capturesR argsR
    refine .invoked code pair ?_ ?_
    · intro target
      apply terminal_iff
      apply eval_terminal
      apply Eval.call
      rw [machineL]
      cases pair with
      | returned _ ranL _ => exact ranL
      | blocked _ _ ranL _ => exact block_eval ranL
    · intro target
      apply terminal_iff
      apply eval_terminal
      apply Eval.call
      rw [machineR]
      cases pair with
      | returned _ _ ranR => exact ranR
      | blocked _ _ _ ranR => exact block_eval ranR

theorem start_linked_calls (respects : ActionsRespect primitives ids)
    {requestL requestR : Request m σ results} {exportsL : Tuple m.Val requestL.exports}
    {exportsR : Tuple m.Val requestR.exports} {store : σ}
    (linkedL : requestL.Links primitives (.linked exportsL store))
    (linkedR : requestR.Links primitives (.linked exportsR store))
    (sameParams : requestL.params = requestR.params)
    (callees : ScheduledLambda m ids rename requestR.params results
      (sameParams ▸ exportsL.get requestL.port) (exportsR.get requestR.port))
    (arguments : TupleRelated m ids (sameParams ▸ requestL.arguments) requestR.arguments) :
    ∃ sourceL sourceR, requestL.start primitives = .ok sourceL ∧ requestR.start primitives = .ok sourceR ∧
      CallPair primitives ids rename results sourceL sourceR := by
  cases requestL
  cases requestR
  cases sameParams
  exact ⟨_, _, start_linked linkedL, start_linked linkedR, calls respects callees arguments store⟩

theorem link_then_invoke (respects : ActionsRespect primitives ids)
    {left : Omega Op args outs sigsL} {right : Omega Op args outs sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Ordered Op (renameVertex positions) args outs left.toTerm.region right.toTerm.region)
    {unitL unitR : Nat} (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputL inputR : Tuple m.Val args} (imports : TupleRelated m ids inputL inputR)
    (port : Port outs (.value (.function params results)))
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ)
    (admitted : ∀ {exportsL exportsR : Tuple m.Val outs} {post : σ},
      Links primitives unitL left inputL store (.linked exportsL post) →
      Links primitives unitR right inputR store (.linked exportsR post) →
      TupleRelated m ids exportsL exportsR →
      ScheduledLambda m ids rename params results (exportsL.get port) (exportsR.get port)) :
    DispatchPair primitives ids (renameVertex positions) rename results
      ((request unitL left inputL port argsL store).start primitives)
      ((request unitR right inputR port argsR store).start primitives) := by
  have paired := link_related respects iso schedule identities imports store
  have linkedL : Links primitives unitL left inputL store (link primitives unitL left inputL store) := link_spec
  have linkedR : Links primitives unitR right inputR store (link primitives unitR right inputR store) := link_spec
  generalize link primitives unitL left inputL store = outcomeL at paired linkedL
  generalize link primitives unitR right inputR store = outcomeR at paired linkedR
  cases paired with
  | undefined address identity sites stopped =>
    rw [(start_error_iff (request := request unitL left inputL port argsL store) (primitives := primitives)).mpr linkedL,
      (start_error_iff (request := request unitR right inputR port argsR store) (primitives := primitives)).mpr linkedR]
    exact .linkBlocked address identity sites stopped
  | linked exports post =>
    rw [start_linked (request := request unitL left inputL port argsL store) (primitives := primitives) linkedL,
      start_linked (request := request unitR right inputR port argsR store) (primitives := primitives) linkedR]
    exact .invoked (calls respects (admitted linkedL linkedR exports) arguments post)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Proofs
