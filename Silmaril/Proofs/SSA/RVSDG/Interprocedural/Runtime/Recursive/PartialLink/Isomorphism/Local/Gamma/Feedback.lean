module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Relation (ReflTransGen TransGen)
open SingleTheta (Carries)
open Continuation.Descent (Pending)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {outs ports carried finalL finalR : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
variable {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
variable {first current next : Carries m ids σ carried}
variable {outcomeL outcomeR : Continuation.Partial.Outcome m σ carried}

private theorem activation (input : Carries m ids σ carried)
    (observed : RegionPair primitives ids mapping left right input.left input.right input.store) :
    Activation primitives mapping left right input ∨ ∃ next, IterationPair primitives left right input next := by
  cases observed with
  | blocked stopped => exact .inl (.blocked stopped)
  | productive run => exact .inl (.inner run)
  | @returned _ _ store paired ranL ranR =>
    cases paired with
    | cons relatedTag values =>
      cases relatedTag with
      | control tag =>
        cases selected : (tag.val == 1) with
        | false => exact .inl (.exited (tag := .control tag) selected values ranL ranR)
        | true => exact .inr ⟨⟨_, _, values, store⟩, ⟨_, ranL, selected⟩, ⟨_, ranR, selected⟩⟩

theorem classify
    (observe : ∀ input : Carries m ids σ carried,
      RegionPair primitives ids mapping left right input.left input.right input.store)
    (first : Carries m ids σ carried) : LoopPair primitives mapping left right first := by
  classical
  by_cases reached : ∃ current, ReflTransGen (IterationPair primitives left right) first current ∧
      Activation primitives mapping left right current
  · obtain ⟨_, completed, observed⟩ := reached
    exact .activation completed observed
  · apply LoopPair.outer
    apply InfiniteTrace.coinduct (ReflTransGen (IterationPair primitives left right) first) ?_ .refl
    intro current completed
    rcases activation current (observe current) with stopped | ⟨next, continued⟩
    · exact False.elim (reached ⟨current, completed, stopped⟩)
    · exact ⟨next, continued, completed.tail continued⟩

theorem rewind (completed : ReflTransGen (IterationPair primitives left right) first current)
    (later : Eval primitives (.iteration left current.left) current.store outcomeL ∧
      Eval primitives (.iteration right current.right) current.store outcomeR) :
    Eval primitives (.iteration left first.left) first.store outcomeL ∧
    Eval primitives (.iteration right first.right) first.store outcomeR := by
  induction completed with
  | refl => exact later
  | tail _ step ih =>
    obtain ⟨⟨_, ranL, feedbackL⟩, ⟨_, ranR, feedbackR⟩⟩ := step
    exact ih ⟨.again ranL feedbackL later.1, .again ranR feedbackR later.2⟩

theorem left_completed (completed : ReflTransGen (IterationPair primitives left right) first current) :
    ReflTransGen (Feedback.Iteration primitives left) (first.left, first.store) (current.left, current.store) := by
  induction completed with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.1

theorem right_completed (completed : ReflTransGen (IterationPair primitives left right) first current) :
    ReflTransGen (Feedback.Iteration primitives right) (first.right, first.store) (current.right, current.store) := by
  induction completed with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.2

theorem iteration_steps (paired : IterationPair primitives left right first next)
    (parentL : Continuation.Stack m carried finalL) (parentR : Continuation.Stack m carried finalR) :
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsL left (first.left, first.store)).config parentL)
      ((Feedback.Restart.mk carried sigsL left (next.left, next.store)).config parentL) ∧
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsR right (first.right, first.store)).config parentR)
      ((Feedback.Restart.mk carried sigsR right (next.right, next.store)).config parentR) :=
  ⟨paired.1.steps parentL, paired.2.steps parentR⟩

theorem outer_runs (paired : InfiniteTrace (IterationPair primitives left right) first) :
    Feedback.Run primitives left (first.left, first.store) ∧
      Feedback.Run primitives right (first.right, first.store) :=
  ⟨InfiniteTrace.map (R := IterationPair primitives left right) (S := Feedback.Iteration primitives left)
      (fun input => (input.left, input.store)) (fun _ _ step => step.1) paired,
    InfiniteTrace.map (R := IterationPair primitives left right) (S := Feedback.Iteration primitives right)
      (fun input => (input.right, input.store)) (fun _ _ step => step.2) paired⟩

/-- Lift a common feedback witness through finite syntax-directed routes.
The chosen inner restart targets and the shared stream remain fixed. -/
theorem productive_map {jobL jobR : Job m outs} {outerL outerR : Job m ports} {store entryStore : σ}
    (run : ProductivePair primitives ids jobL jobR store)
    (liftL : ∀ {target : Feedback.Restart m σ} {pending : Pending m target.carried outs},
      Feedback.Reaches primitives jobL store target pending →
      ∃ saved, Feedback.Reaches primitives outerL entryStore target saved)
    (liftR : ∀ {target : Feedback.Restart m σ} {pending : Pending m target.carried outs},
      Feedback.Reaches primitives jobR store target pending →
      ∃ saved, Feedback.Reaches primitives outerR entryStore target saved) :
    ProductivePair primitives ids outerL outerR entryStore := by
  cases run with
  | reached paired ranL ranR =>
    obtain ⟨_, enteredL⟩ := liftL ranL
    obtain ⟨_, enteredR⟩ := liftR ranR
    exact .reached paired enteredL enteredR
  | feedback paired ranL ranR =>
    obtain ⟨_, enteredL⟩ := liftL ranL
    obtain ⟨_, enteredR⟩ := liftR ranR
    exact .feedback paired enteredL enteredR

private theorem replay_productive {jobL jobR : Job m outs} {store : σ}
    {pendingL pendingR : Pending m carried outs}
    (paired : InfiniteTrace (IterationPair primitives left right) first)
    (enteredL : Feedback.Reaches primitives jobL store ⟨carried, sigsL, left, (first.left, first.store)⟩ pendingL)
    (enteredR : Feedback.Reaches primitives jobR store ⟨carried, sigsR, right, (first.right, first.store)⟩ pendingR)
    (frameL : Continuation.Stack m outs finalL) (frameR : Continuation.Stack m outs finalR) :
    InfiniteTrace (Step primitives) ⟨.eval jobL frameL, store⟩ ∧
    InfiniteTrace (Step primitives) ⟨.eval jobR frameR, store⟩ := by
  obtain ⟨liveL, liveR⟩ := outer_runs paired
  exact ⟨InfiniteTrace.of_steps (enteredL.steps frameL) (liveL.infinite (pendingL.push frameL)),
    InfiniteTrace.of_steps (enteredR.steps frameR) (liveR.infinite (pendingR.push frameR))⟩

theorem productive_infinite {jobL jobR : Job m outs} {store : σ}
    (run : ProductivePair primitives ids jobL jobR store)
    (frameL : Continuation.Stack m outs finalL) (frameR : Continuation.Stack m outs finalR) :
    InfiniteTrace (Step primitives) ⟨.eval jobL frameL, store⟩ ∧
    InfiniteTrace (Step primitives) ⟨.eval jobR frameR, store⟩ := by
  cases run with
  | reached paired reachedL reachedR => exact replay_productive paired reachedL reachedR frameL frameR
  | feedback paired reachedL reachedR => exact replay_productive paired reachedL reachedR frameL frameR

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
