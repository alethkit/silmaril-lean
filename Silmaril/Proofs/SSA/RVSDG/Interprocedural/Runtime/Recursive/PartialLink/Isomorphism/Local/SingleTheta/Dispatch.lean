module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Iterations
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open PartialLink.Invocation (start_linked start_error_iff)
open Isomorphism.Invocation (request loopVertex)
open Isomorphism.Proofs (LocalsRelated read_same)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {rename : Renaming}
variable {args outs carried params results : Ports (Ty V S)}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}

private theorem prepend_related {context : Ports (Ty V S)}
    {capturesL capturesR : Tuple m.Val context} {argsL argsR : Tuple m.Val params}
    (captures : TupleRelated m ids capturesL capturesR) (arguments : TupleRelated m ids argsL argsR) :
    TupleRelated m ids (prependContext argsL capturesL) (prependContext argsR capturesR) := by
  induction context with
  | nil => cases captures; exact arguments
  | cons _ _ ih => cases captures with | cons head tail => exact .cons head (ih tail)

private theorem open_lambda {context : Ports (Ty V S)}
    (initial : Wires (context ++ params) [] carried) (body : Body Op carried sigs)
    (outputs : Wires (context ++ params) [carried] results)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    Job.openClosure m (.closure captures (code initial body outputs).toGraph) arguments =
      .region (code initial body outputs) (prependContext arguments captures) PUnit.unit :=
  congrArg (fun term => Job.region (m := m) (past := []) term (prependContext arguments captures) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph (code initial body outputs))

private theorem enter_loop {context : Ports (Ty V S)}
    (initial : Wires (context ++ params) [] carried) (body : Body Op carried sigs)
    (outputs : Wires (context ++ params) [carried] results)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) (store : σ) :
    ReflTransGen (Step primitives)
      ⟨Continuation.start (.call (.closure captures (code initial body outputs).toGraph) arguments), store⟩
      (restart body outputs (prependContext arguments captures)
        (initial.read (prependContext arguments captures) PUnit.unit, store)) := by
  let entry := prependContext arguments captures
  let target : Feedback.Restart m σ := ⟨carried, sigs, embed body.toTerm, initial.read entry PUnit.unit, store⟩
  let pending : Pending m carried results := .bind (past := []) (.ret outputs) entry PUnit.unit .empty
  have reached : Feedback.Reaches primitives (.region (code initial body outputs) entry PUnit.unit)
      store target pending :=
    .inside (node := loopVertex initial sigs) (.theta (.restart (input := target.input) (current := target.input) .refl))
  rw [← open_lambda initial body outputs captures arguments] at reached
  exact (Feedback.Reaches.call reached).steps .halt

private theorem terminal_of_eval {job : Job m results} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ results}
    (ran : Eval primitives job store outcome) : TerminalOutcome primitives ⟨Continuation.start job, store⟩ outcome := by
  intro target
  apply TerminalPath.target_iff
  refine ⟨ran.steps .halt, ?_⟩
  cases outcome with
  | returned => exact fun _ stepped => _root_.Part.notMem_none _ stepped
  | blocked => exact fun _ => (ran.blocks .halt).no_step

theorem calls (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ScheduledLambda m ids rename params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ) :
    CallPair primitives ids rename results
      ⟨Continuation.start (.call calleeL argsL), store⟩
      ⟨Continuation.start (.call calleeR argsR), store⟩ := by
  cases callees with
  | @closure context carried sigsL sigsR capturesL capturesR left right captures initial outputs admitted =>
    let entryL := prependContext argsL capturesL
    let entryR := prependContext argsR capturesR
    have related := prepend_related captures arguments
    let input : Carries m ids σ carried :=
      ⟨initial.read entryL PUnit.unit, initial.read entryR PUnit.unit,
        read_same related LocalsRelated.empty initial, store⟩
    rcases classify admitted respects input with ⟨_, _, finished⟩ | productive
    · obtain ⟨ranL, ranR⟩ := evaluates finished
      obtain ⟨current, completed, terminal⟩ := finished
      cases terminal with
      | @exited _ _ _ finalStore _ values _ _ =>
        have locals := LocalsRelated.empty.snoc (fun _ _ equal => equal) rfl values
        refine .returned (store := finalStore) (read_same related locals outputs) ?_ ?_
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bind (node := loopVertex initial sigsL) (.theta ranL) (.ret outputs _ _ _)
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bind (node := loopVertex initial sigsR) (.theta ranR) (.ret outputs _ _ _)
      | blocked location sites firstL firstR =>
        refine .blocked (entryL := entryL) (entryR := entryR) outputs ⟨current, completed, .blocked location sites firstL firstR⟩ ?_ ?_
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bindBlocked (node := loopVertex initial sigsL) (.theta ranL)
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bindBlocked (node := loopVertex initial sigsR) (.theta ranR)
    · exact .productive outputs productive
        (enter_loop initial left outputs capturesL argsL store)
        (enter_loop initial right outputs capturesR argsR store)

private theorem terminal_excludes_infinite {source : Config m σ results}
    {outcome : Continuation.Partial.Outcome m σ results}
    (ran : TerminalOutcome primitives source outcome) : ¬ InfiniteTrace (Step primitives) source := by
  have reached := (ran (outcome.atStack .halt)).mpr rfl
  exact RightUnique.not_infinite_of_final (R := Step primitives)
    (fun _ _ _ a b => _root_.Part.mem_unique a b) reached.path reached.terminal

theorem infinite_iff {sourceL sourceR : Config m σ results}
    (related : CallPair primitives ids rename results sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR := by
  cases related with
  | returned _ left right =>
    exact iff_of_false (terminal_excludes_infinite left) (terminal_excludes_infinite right)
  | blocked _ _ left right =>
    exact iff_of_false (terminal_excludes_infinite left) (terminal_excludes_infinite right)
  | productive outputs paired arrivedL arrivedR =>
    obtain ⟨left, right⟩ := feedback_infinite paired outputs _ _
    exact ⟨fun _ => InfiniteTrace.of_steps arrivedR right, fun _ => InfiniteTrace.of_steps arrivedL left⟩

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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Proofs
