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

theorem classify (admitted : Gamma.CodePair Op mapping left right)
    (respects : ActionsRespect primitives ids) (first : Carries m ids σ carried) :
    LoopPair primitives mapping left right first :=
  Gamma.loop_observations (fun input => Gamma.regions admitted respects input.related input.store) first

theorem rewind (completed : ReflTransGen (IterationPair primitives left right) first current)
    (later : Eval primitives (.iteration left current.left) current.store outcomeL ∧
      Eval primitives (.iteration right current.right) current.store outcomeR) :
    Eval primitives (.iteration left first.left) first.store outcomeL ∧
    Eval primitives (.iteration right first.right) first.store outcomeR :=
  Gamma.IterationPair.replay completed later

theorem left_completed (completed : ReflTransGen (IterationPair primitives left right) first current) :
    ReflTransGen (Feedback.Iteration primitives left) (first.left, first.store) (current.left, current.store) :=
  (Gamma.IterationPair.completed completed).1

theorem right_completed (completed : ReflTransGen (IterationPair primitives left right) first current) :
    ReflTransGen (Feedback.Iteration primitives right) (first.right, first.store) (current.right, current.store) :=
  (Gamma.IterationPair.completed completed).2

theorem iteration_steps (paired : IterationPair primitives left right first next)
    (parentL : Continuation.Stack m carried finalL) (parentR : Continuation.Stack m carried finalR) :
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsL left (first.left, first.store)).config parentL)
      ((Feedback.Restart.mk carried sigsL left (next.left, next.store)).config parentL) ∧
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsR right (first.right, first.store)).config parentR)
      ((Feedback.Restart.mk carried sigsR right (next.right, next.store)).config parentR) :=
  Gamma.IterationPair.steps paired parentL parentR

theorem outer_runs (paired : InfiniteTrace (IterationPair primitives left right) first) :
    Feedback.Run primitives left (first.left, first.store) ∧
      Feedback.Run primitives right (first.right, first.store) :=
  Gamma.IterationPair.runs paired

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
