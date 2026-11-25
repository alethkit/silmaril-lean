module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms
import Silmaril.Foundations.InfiniteTrace.Deterministic

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Proofs

open Continuation.Partial
open Relation (ReflTransGen TransGen)
open SingleTheta (Carries)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {carried finalL finalR : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
variable {left : Body Op carried sigsL} {right : Body Op carried sigsR}
variable {first current next : Carries m ids σ carried}
variable {outcomeL outcomeR : Continuation.Partial.Outcome m σ carried}

private theorem activation (admitted : Gamma.CodePair Op mapping left right)
    (respects : ActionsRespect primitives ids) (input : Carries m ids σ carried) :
    Activation primitives mapping left right input ∨ ∃ next, IterationPair primitives left right input next := by
  cases Gamma.regions admitted respects input.related input.store with
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

theorem classify (admitted : Gamma.CodePair Op mapping left right)
    (respects : ActionsRespect primitives ids) (first : Carries m ids σ carried) :
    LoopPair primitives mapping left right first := by
  classical
  by_cases reached : ∃ current, ReflTransGen (IterationPair primitives left right) first current ∧
      Activation primitives mapping left right current
  · obtain ⟨_, completed, observed⟩ := reached
    exact .activation completed observed
  · apply LoopPair.outer
    apply InfiniteTrace.coinduct (ReflTransGen (IterationPair primitives left right) first) ?_ .refl
    intro current completed
    rcases activation admitted respects current with stopped | ⟨next, continued⟩
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

private theorem feedback_unique : Relator.RightUnique (Feedback.Iteration primitives left) := by
  intro input nextL nextR first second
  obtain ⟨tagL, ranL, _⟩ := first
  obtain ⟨tagR, ranR, _⟩ := second
  have same := RightUnique.reach_final_eq (R := Step (final := Theta.BodyResults carried) primitives)
    (fun _ _ _ a b => _root_.Part.mem_unique a b) (ranL.steps .halt) (ranR.steps .halt)
    (fun _ stepped => _root_.Part.notMem_none _ stepped) (fun _ stepped => _root_.Part.notMem_none _ stepped)
  have packed : (Tuple.cons tagL nextL.1, nextL.2) = (Tuple.cons tagR nextR.1, nextR.2) :=
    Option.some.inj (congrArg Config.result same)
  let dropTag : Tuple m.Val (Theta.BodyResults carried) → Tuple m.Val carried
    | .cons _ values => values
  exact congrArg (fun (value : Tuple m.Val (Theta.BodyResults carried) × σ) => (dropTag value.1, value.2)) packed

theorem inner_excludes_outer (completed : ReflTransGen (IterationPair primitives left right) first current)
    (inner : Gamma.ProductivePair primitives ids (.region left current.left PUnit.unit)
      (.region right current.right PUnit.unit) current.store) :
    ¬ InfiniteTrace (IterationPair primitives left right) first := by
  intro outer
  have runs := (outer_runs outer).1
  have suffix := RightUnique.infinite_of_reach feedback_unique (left_completed completed) runs
  obtain ⟨_, ⟨_, returned, _⟩, _⟩ := suffix.unfold
  have infinite := (inner.infinite .halt .halt).1
  exact RightUnique.not_infinite_of_final (R := Step (final := Theta.BodyResults carried) primitives)
    (fun _ _ _ a b => _root_.Part.mem_unique a b) (returned.steps .halt)
    (fun _ stepped => _root_.Part.notMem_none _ stepped) infinite

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Proofs
