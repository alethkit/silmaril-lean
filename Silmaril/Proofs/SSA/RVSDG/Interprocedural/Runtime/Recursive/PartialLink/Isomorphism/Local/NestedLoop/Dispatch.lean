module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Iterations
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open PartialLink.Invocation (start_linked start_error_iff)
open Isomorphism.Invocation (request loopVertex)
open Isomorphism.Proofs (LocalsRelated read_same)
open SingleTheta (Carries)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
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
    (outputs : Wires (context ++ params) [carried] outs)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    Job.openClosure m (.closure captures (code initial body outputs).toGraph) arguments =
      .region (code initial body outputs) (prependContext arguments captures) PUnit.unit :=
  congrArg (fun term => Job.region (m := m) (past := []) term (prependContext arguments captures) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph (code initial body outputs))

private theorem enter_loop {context : Ports (Ty V S)}
    (initial : Wires (context ++ params) [] carried) (body : Body Op carried sigs)
    (outputs : Wires (context ++ params) [carried] outs)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) (store : σ) :
    ReflTransGen (Step primitives)
      ⟨Continuation.start (.call (.closure captures (code initial body outputs).toGraph) arguments), store⟩
      (restart body outputs (prependContext arguments captures)
        (initial.read (prependContext arguments captures) PUnit.unit, store)) := by
  let entry := prependContext arguments captures
  let target : Feedback.Restart m σ := ⟨carried, sigs, body, initial.read entry PUnit.unit, store⟩
  let pending : Pending m carried outs := .bind (past := []) (.ret outputs) entry PUnit.unit .empty
  have reached : Feedback.Reaches primitives (.region (code initial body outputs) entry PUnit.unit)
      store target pending :=
    .inside (node := loopVertex initial sigs) (.theta (.restart (input := target.input) (current := target.input) .refl))
  rw [← open_lambda initial body outputs captures arguments] at reached
  exact (Feedback.Reaches.call reached).steps .halt

private theorem enter_active {body : Body Op carried sigs} {input current : Tuple m.Val carried × σ}
    (outputs : Wires args [carried] outs) (entry : Tuple m.Val args)
    (completed : ReflTransGen (Feedback.Iteration primitives body) input current) :
    ReflTransGen (Step primitives) (restart body outputs entry input) (active body outputs entry current) :=
  ((Feedback.Reaches.restart completed).steps (.resume (past := []) (.ret outputs) entry PUnit.unit .halt)).tail
    (.of_next_some rfl)

private theorem terminal_of_eval {job : Job m outs} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (ran : Eval primitives job store outcome) :
    SingleTheta.TerminalOutcome primitives ⟨Continuation.start job, store⟩ outcome := by
  intro target
  apply TerminalPath.target_iff
  refine ⟨ran.steps .halt, ?_⟩
  cases outcome with
  | returned => exact fun _ stepped => _root_.Part.notMem_none _ stepped
  | blocked => exact fun _ => (ran.blocks .halt).no_step

theorem calls (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ScheduledLambda m ids mapping params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ) :
    CallPair primitives ids mapping results
      ⟨Continuation.start (.call calleeL argsL), store⟩
      ⟨Continuation.start (.call calleeR argsR), store⟩ := by
  cases callees with
  | @closure context carried sigsL sigsR capturesL capturesR left right captures initial outputs _ admitted =>
    let entryL := prependContext argsL capturesL
    let entryR := prependContext argsR capturesR
    have related := prepend_related captures arguments
    let first : Carries m ids σ carried := ⟨initial.read entryL PUnit.unit, initial.read entryR PUnit.unit,
      read_same related LocalsRelated.empty initial, store⟩
    have enteredL := enter_loop (primitives := primitives) initial left outputs capturesL argsL store
    have enteredR := enter_loop (primitives := primitives) initial right outputs capturesR argsR store
    cases classify admitted respects first with
    | outer live => exact .outer outputs live enteredL enteredR
    | activation completed observed =>
      cases observed with
      | @exited _ _ _ finalStore exits values bodyL bodyR =>
        have ran := rewind completed ⟨Eval.stop bodyL exits, Eval.stop bodyR exits⟩
        have locals := LocalsRelated.empty.snoc (fun _ _ same => same) rfl values
        refine .returned (store := finalStore) (read_same related locals outputs) ?_ ?_
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bind (node := loopVertex initial sigsL) (.theta ran.1) (.ret outputs _ _ _)
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bind (node := loopVertex initial sigsR) (.theta ran.2) (.ret outputs _ _ _)
      | blocked stopped =>
        have body := stopped.evals
        have ran := rewind completed ⟨Eval.loopBlocked body.1, Eval.loopBlocked body.2⟩
        refine .blocked (entryL := entryL) (entryR := entryR) outputs completed stopped ?_ ?_
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bindBlocked (node := loopVertex initial sigsL) (.theta ran.1)
        · apply terminal_of_eval
          apply Eval.call
          rw [open_lambda]
          exact .bindBlocked (node := loopVertex initial sigsR) (.theta ran.2)
      | inner live =>
        exact .inner outputs completed live (enteredL.trans (enter_active outputs entryL (left_completed completed)))
          (enteredR.trans (enter_active outputs entryR (right_completed completed)))

private theorem terminal_excludes_infinite {source : Config m σ outs}
    {outcome : Continuation.Partial.Outcome m σ outs}
    (ran : SingleTheta.TerminalOutcome primitives source outcome) : ¬ InfiniteTrace (Step primitives) source := by
  have reached := (ran (outcome.atStack .halt)).mpr rfl
  exact RightUnique.not_infinite_of_final (R := Step primitives)
    (fun _ _ _ a b => _root_.Part.mem_unique a b) reached.path reached.terminal

private theorem inner_infinite {left : Body Op carried sigsL} {right : Body Op carried sigsR}
    {sourceL sourceR : Config m σ outs} {entryL entryR : Tuple m.Val args} {current : Carries m ids σ carried}
    (outputs : Wires args [carried] outs)
    (live : Gamma.ProductivePair primitives ids (.region left current.left PUnit.unit)
      (.region right current.right PUnit.unit) current.store)
    (enteredL : ReflTransGen (Step primitives) sourceL (active left outputs entryL (current.left, current.store)))
    (enteredR : ReflTransGen (Step primitives) sourceR (active right outputs entryR (current.right, current.store))) :
    InfiniteTrace (Step primitives) sourceL ∧ InfiniteTrace (Step primitives) sourceR := by
  obtain ⟨ranL, ranR⟩ := live.infinite
    (.loop left (.resume (past := []) (.ret outputs) entryL PUnit.unit .halt))
    (.loop right (.resume (past := []) (.ret outputs) entryR PUnit.unit .halt))
  exact ⟨InfiniteTrace.of_steps enteredL ranL, InfiniteTrace.of_steps enteredR ranR⟩

private theorem outer_infinite {left : Body Op carried sigsL} {right : Body Op carried sigsR}
    {sourceL sourceR : Config m σ outs} {entryL entryR : Tuple m.Val args} {first : Carries m ids σ carried}
    (outputs : Wires args [carried] outs) (live : InfiniteTrace (IterationPair primitives left right) first)
    (enteredL : ReflTransGen (Step primitives) sourceL (restart left outputs entryL (first.left, first.store)))
    (enteredR : ReflTransGen (Step primitives) sourceR (restart right outputs entryR (first.right, first.store))) :
    InfiniteTrace (Step primitives) sourceL ∧ InfiniteTrace (Step primitives) sourceR := by
  obtain ⟨runL, runR⟩ := outer_runs live
  exact ⟨InfiniteTrace.of_steps enteredL (runL.infinite _), InfiniteTrace.of_steps enteredR (runR.infinite _)⟩

theorem infinite_iff {sourceL sourceR : Config m σ outs}
    (paired : CallPair primitives ids mapping outs sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR := by
  cases paired with
  | returned _ ranL ranR =>
    exact iff_of_false (terminal_excludes_infinite ranL) (terminal_excludes_infinite ranR)
  | blocked _ _ _ ranL ranR =>
    exact iff_of_false (terminal_excludes_infinite ranL) (terminal_excludes_infinite ranR)
  | inner outputs _ live enteredL enteredR =>
    have ran := inner_infinite outputs live enteredL enteredR
    exact ⟨fun _ => ran.2, fun _ => ran.1⟩
  | outer outputs live enteredL enteredR =>
    have ran := outer_infinite outputs live enteredL enteredR
    exact ⟨fun _ => ran.2, fun _ => ran.1⟩

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
      ScheduledLambda m ids mapping params results (exportsL.get port) (exportsR.get port)) :
    DispatchPair primitives ids (renameVertex positions) mapping results
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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Proofs
