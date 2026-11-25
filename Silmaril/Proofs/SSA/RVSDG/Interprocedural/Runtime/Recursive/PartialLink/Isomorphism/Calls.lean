module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Defs
public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Initializers
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
public import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Proofs

open Isomorphism.Proofs (EvaluationsRelated initializer_related LocalsRelated read_same)
open Continuation.Partial
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ}
variable {args params results carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
variable {body : Term Op carried [] sigs (Theta.BodyResults carried)}

private structure LoopInputs (m : Machine.{u, v, w} Op) (ids : GlobalRel) (σ : Type (max u v w))
    (carried : Ports (Ty V S)) where
  left : Tuple m.Val carried
  right : Tuple m.Val carried
  paired : TupleRelated m ids left right
  store : σ

private abbrev LoopsFinish (primitives : Primitives m σ)
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (input : LoopInputs m ids σ carried) :=
  EvaluationsRelated primitives ids (.iteration (embed body) input.left) (.iteration (embed body) input.right)
    input.store

private abbrev LoopsRestart (primitives : Primitives m σ)
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (input next : LoopInputs m ids σ carried) :=
  Feedback.Iteration primitives (embed body) (input.left, input.store) (next.left, next.store) ∧
  Feedback.Iteration primitives (embed body) (input.right, input.store) (next.right, next.store)

private theorem loop_progress (respects : ActionsRespect primitives ids) (input : LoopInputs m ids σ carried) :
    LoopsFinish primitives body input ∨ ∃ next, LoopsRestart primitives body input next := by
  obtain ⟨_, _, ranL, ranR, paired⟩ :=
    initializer_related respects body input.paired LocalsRelated.empty input.store
  cases paired with
  | blocked sites store =>
    exact .inl ⟨_, _, .loopBlocked ranL, .loopBlocked ranR, .blocked sites store⟩
  | returned values store =>
    cases values with
    | cons selector outputs =>
      cases selector with
      | control tag =>
        cases feedback : (tag.val == 1) with
        | false => exact .inl ⟨_, _, .stop ranL feedback, .stop ranR feedback, .returned outputs store⟩
        | true => exact .inr ⟨⟨_, _, outputs, store⟩, ⟨_, ranL, feedback⟩, ⟨_, ranR, feedback⟩⟩

private theorem finish_of_restarts {input current : LoopInputs m ids σ carried}
    (path : ReflTransGen (LoopsRestart primitives body) input current) :
    LoopsFinish primitives body current → LoopsFinish primitives body input := by
  induction path with
  | refl => exact id
  | tail _ next ih =>
    rintro ⟨_, _, laterL, laterR, paired⟩
    obtain ⟨⟨_, ranL, againL⟩, ⟨_, ranR, againR⟩⟩ := next
    exact ih ⟨_, _, .again ranL againL laterL, .again ranR againR laterR, paired⟩

private theorem loops (respects : ActionsRespect primitives ids) (input : LoopInputs m ids σ carried) :
    LoopsFinish primitives body input ∨
      Feedback.Run primitives (embed body) (input.left, input.store) ∧
      Feedback.Run primitives (embed body) (input.right, input.store) := by
  classical
  by_cases finished : LoopsFinish primitives body input
  · exact .inl finished
  have trail : InfiniteTrace (LoopsRestart primitives body) input := by
    apply InfiniteTrace.coinduct (ReflTransGen (LoopsRestart primitives body) input) ?_ .refl
    intro current reached
    rcases loop_progress (body := body) respects current with done | ⟨next, restarted⟩
    · exact False.elim (finished (finish_of_restarts reached done))
    · exact ⟨next, restarted, reached.tail restarted⟩
  refine .inr ⟨?_, ?_⟩
  · exact InfiniteTrace.map (R := LoopsRestart primitives body)
      (S := Feedback.Iteration primitives (embed body))
      (fun current => (current.left, current.store)) (fun _ _ step => step.1) trail
  · exact InfiniteTrace.map (R := LoopsRestart primitives body)
      (S := Feedback.Iteration primitives (embed body))
      (fun current => (current.right, current.store)) (fun _ _ step => step.2) trail

private abbrev JobsRelated (primitives : Primitives m σ) (ids : GlobalRel)
    (left right : Job m results) (store : σ) :=
  EvaluationsRelated primitives ids left right store ∨
    Feedback.Productive primitives left store ∧ Feedback.Productive primitives right store

private theorem loop_productive (initial : Wires args [] carried)
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (outputs : Wires args [carried] results)
    (input : Tuple m.Val args) (store : σ)
    (ran : Feedback.Run primitives (embed body) (initial.read input PUnit.unit, store)) :
    Feedback.Productive primitives
      (.region (.bind (loopVertex initial sigs) (fun _ => embed body) (.ret outputs)) input PUnit.unit) store := by
  let target : Feedback.Restart m σ := ⟨carried, sigs, embed body, initial.read input PUnit.unit, store⟩
  let frames : Continuation.Descent.Pending m carried results :=
    .bind (past := []) (.ret outputs) input PUnit.unit .empty
  exact ⟨target, frames, .inside (node := loopVertex initial sigs)
    (.theta (.restart (input := target.input) (current := target.input) .refl)), ran⟩

private theorem body_related (respects : ActionsRespect primitives ids)
    {term : NestedTheta.Term (Instruction Op) args [] sigs results}
    (admitted : SharedCode Op args results term)
    {inputL inputR : Tuple m.Val args} (related : TupleRelated m ids inputL inputR) (store : σ) :
    JobsRelated primitives ids (.region term inputL PUnit.unit) (.region term inputR PUnit.unit) store := by
  cases admitted with
  | acyclic term =>
    exact .inl (initializer_related respects term related LocalsRelated.empty store)
  | theta initial body outputs =>
    have carried := read_same related LocalsRelated.empty initial
    let input : LoopInputs m ids σ _ := ⟨_, _, carried, store⟩
    rcases loops (body := body) respects input with ⟨_, _, ranL, ranR, observations⟩ | ⟨runL, runR⟩
    · left
      cases observations with
      | returned values store =>
        have locals := LocalsRelated.empty.snoc (fun _ _ equal => equal) rfl values
        exact ⟨_, _, .bind (.theta ranL) (.ret outputs _ _ _), .bind (.theta ranR) (.ret outputs _ _ _),
          .returned (read_same related locals outputs) store⟩
      | blocked sites store =>
        exact ⟨_, _, .bindBlocked (.theta ranL), .bindBlocked (.theta ranR), .blocked sites store⟩
    · exact .inr ⟨loop_productive initial body outputs inputL store runL,
        loop_productive initial body outputs inputR store runR⟩

private theorem prepend_related {context : Ports (Ty V S)}
    {capturesL capturesR : Tuple m.Val context} {argsL argsR : Tuple m.Val params}
    (captures : TupleRelated m ids capturesL capturesR) (arguments : TupleRelated m ids argsL argsR) :
    TupleRelated m ids (prependContext argsL capturesL) (prependContext argsR capturesR) := by
  induction context with
  | nil => cases captures; exact arguments
  | cons _ _ ih => cases captures with | cons head tail => exact .cons head (ih tail)

private theorem open_lambda {context : Ports (Ty V S)}
    (body : NestedTheta.Term (Instruction Op) (context ++ params) [] sigs results)
    (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    Job.openClosure m (.closure captures body.toGraph) arguments =
      .region body (prependContext arguments captures) PUnit.unit :=
  congrArg (fun term => Job.region (m := m) (past := []) term (prependContext arguments captures) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph body)

private theorem calls (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ValueRelated m ids calleeL calleeR) (code : SharedLambda m params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ) :
    JobsRelated primitives ids (.call calleeL argsL) (.call calleeR argsR) store := by
  cases code with
  | @closure context sigs left right body admitted =>
    have captured : TupleRelated m ids left right := (Recursive.resolve_related callees).1
    have ran := body_related respects admitted (prepend_related captured arguments) store
    have equalL := open_lambda body left argsL
    have equalR := open_lambda body right argsR
    rcases ran with ⟨_, _, ranL, ranR, paired⟩ | ⟨⟨_, _, reachL, runL⟩, ⟨_, _, reachR, runR⟩⟩
    · exact .inl ⟨_, _, .call (equalL.symm ▸ ranL), .call (equalR.symm ▸ ranR), paired⟩
    · exact .inr ⟨⟨_, _, .call (equalL.symm ▸ reachL), runL⟩, ⟨_, _, .call (equalR.symm ▸ reachR), runR⟩⟩

theorem call_observations (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ValueRelated m ids calleeL calleeR) (code : SharedLambda m params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ)
    (rename : Nat → Nat) :
    ObservationsRelated primitives ids rename results
      (.ok ⟨Continuation.start (.call calleeL argsL), store⟩)
      (.ok ⟨Continuation.start (.call calleeR argsR), store⟩) := by
  rcases calls respects callees code arguments store with ⟨_, _, ranL, ranR, paired⟩ | ⟨runL, runR⟩
  · cases paired with
    | returned values => exact .returned values (ranL.steps .halt) (ranR.steps .halt)
    | blocked sites =>
      exact .invocationBlocked sites (ranL.steps .halt) (ranR.steps .halt) (ranL.blocks .halt) (ranR.blocks .halt)
  · exact .diverges (runL.infinite .halt) (runR.infinite .halt)

private theorem return_ends {source : Config m σ results} {value : Tuple m.Val results} {store : σ}
    (path : ReflTransGen (Step primitives) source ⟨.returned value .halt, store⟩) :
    ¬ InfiniteTrace (Step primitives) source :=
  RightUnique.not_infinite_of_final (R := Step (final := results) primitives) (fun _ _ _ left right => _root_.Part.mem_unique left right)
    path (fun _ stepped => _root_.Part.notMem_none _ stepped)

theorem infinite_iff {rename : Nat → Nat} {left right : Config m σ results}
    (paired : ObservationsRelated primitives ids rename results (.ok left) (.ok right)) :
    InfiniteTrace (Step primitives) left ↔ InfiniteTrace (Step primitives) right := by
  cases paired with
  | returned _ returnedL returnedR =>
    exact iff_of_false (return_ends returnedL) (return_ends returnedR)
  | invocationBlocked _ pathL pathR blockedL blockedR =>
    exact iff_of_false (no_infinite_of_reaches_blocked pathL blockedL) (no_infinite_of_reaches_blocked pathR blockedR)
  | diverges runsL runsR => exact ⟨fun _ => runsR, fun _ => runsL⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Proofs
