module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Proofs

open Continuation.Partial
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {rename : Renaming}
variable {args carried results : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {left : Body Op carried sigsL} {right : Body Op carried sigsR}
variable {input current : Carries m ids σ carried}
variable {outcomeL outcomeR : Continuation.Partial.Outcome m σ carried}

private theorem activation (admitted : OrderedGraph rename left right)
    (respects : ActionsRespect primitives ids) (input : Carries m ids σ carried) :
    (∃ outL outR, FinalIteration primitives rename left right input outL outR) ∨
      ∃ next, FeedbackPair primitives left right input next := by
  obtain ⟨_, _, pair⟩ := Local.graph_evaluate admitted respects input.related input.store
  cases pair with
  | blocked location sites ranL ranR =>
    exact .inl ⟨_, _, .blocked location sites ranL ranR⟩
  | @returned _ _ store values ranL ranR =>
    cases values with
    | cons selector carried =>
      cases selector with
      | control tag =>
        cases selected : (tag.val == 1) with
        | false => exact .inl ⟨_, _, .exited (tag := .control tag) selected carried ranL ranR⟩
        | true => exact .inr ⟨⟨_, _, carried, store⟩, ⟨_, ranL, selected⟩, ⟨_, ranR, selected⟩⟩

/-- Progress at each paired activation supplies both positive feedback
steps unless that activation exits or blocks. -/
theorem classify (admitted : OrderedGraph rename left right) (respects : ActionsRespect primitives ids)
    (input : Carries m ids σ carried) :
    (∃ outL outR, Finishes primitives rename left right input outL outR) ∨
      InfiniteTrace (FeedbackPair primitives left right) input := by
  classical
  by_cases ends : ∃ outL outR, Finishes primitives rename left right input outL outR
  · exact .inl ends
  · right
    apply InfiniteTrace.coinduct (ReflTransGen (FeedbackPair primitives left right) input) ?_ .refl
    intro current completed
    rcases activation admitted respects current with ⟨_, _, final⟩ | ⟨next, feedback⟩
    · exact False.elim (ends ⟨_, _, current, completed, final⟩)
    · exact ⟨next, feedback, completed.tail feedback⟩

private abbrev Evaluates (primitives : Primitives m σ) (left : Body Op carried sigsL) (right : Body Op carried sigsR)
    (input : Carries m ids σ carried) (outcomeL outcomeR : Continuation.Partial.Outcome m σ carried) :=
  Eval primitives (.iteration (embed left.toTerm) input.left) input.store outcomeL ∧
  Eval primitives (.iteration (embed right.toTerm) input.right) input.store outcomeR

private theorem rewind (completed : ReflTransGen (FeedbackPair primitives left right) input current) :
    Evaluates primitives left right current outcomeL outcomeR →
    Evaluates primitives left right input outcomeL outcomeR := by
  induction completed with
  | refl => exact id
  | tail _ step ih =>
    rintro ⟨afterL, afterR⟩
    obtain ⟨⟨_, ranL, againL⟩, ⟨_, ranR, againR⟩⟩ := step
    exact ih ⟨.again ranL againL afterL, .again ranR againR afterR⟩

theorem evaluates (done : Finishes primitives rename left right input outcomeL outcomeR) :
    Eval primitives (.iteration (embed left.toTerm) input.left) input.store outcomeL ∧
    Eval primitives (.iteration (embed right.toTerm) input.right) input.store outcomeR := by
  obtain ⟨_, completed, final⟩ := done
  apply rewind completed
  cases final with
  | exited exits _ ranL ranR => exact ⟨.stop ranL exits, .stop ranR exits⟩
  | blocked _ _ ranL ranR => exact ⟨.loopBlocked ranL.eval, .loopBlocked ranR.eval⟩

theorem feedback_steps {next : Carries m ids σ carried}
    (paired : FeedbackPair primitives left right input next)
    (outputs : Wires args [carried] results) (entryL entryR : Tuple m.Val args) :
    TransGen (Step primitives) (restart left outputs entryL (input.left, input.store))
      (restart left outputs entryL (next.left, next.store)) ∧
    TransGen (Step primitives) (restart right outputs entryR (input.right, input.store))
      (restart right outputs entryR (next.right, next.store)) :=
  ⟨paired.1.steps _, paired.2.steps _⟩

/-- Both projections of the same certificate replay as actual infinite
microsteps, with the parent suffix retained at all restarts. -/
theorem feedback_infinite
    (paired : InfiniteTrace (FeedbackPair primitives left right) input)
    (outputs : Wires args [carried] results) (entryL entryR : Tuple m.Val args) :
    InfiniteTrace (Step primitives) (restart left outputs entryL (input.left, input.store)) ∧
    InfiniteTrace (Step primitives) (restart right outputs entryR (input.right, input.store)) := by
  have leftRun : Feedback.Run primitives (embed left.toTerm) (input.left, input.store) :=
    InfiniteTrace.map (R := FeedbackPair primitives left right) (S := Feedback.Iteration primitives (embed left.toTerm))
      (fun current => (current.left, current.store)) (fun _ _ step => step.1) paired
  have rightRun : Feedback.Run primitives (embed right.toTerm) (input.right, input.store) :=
    InfiniteTrace.map (R := FeedbackPair primitives left right) (S := Feedback.Iteration primitives (embed right.toTerm))
      (fun current => (current.right, current.store)) (fun _ _ step => step.2) paired
  exact ⟨leftRun.infinite _, rightRun.infinite _⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Proofs
