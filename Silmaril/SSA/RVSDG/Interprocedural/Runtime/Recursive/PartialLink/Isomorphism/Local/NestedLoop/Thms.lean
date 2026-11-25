module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Iterations
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop.Dispatch

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop

open Continuation.Partial
open Isomorphism.Invocation (request)
open Relation (ReflTransGen TransGen)
open SingleTheta (Carries)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs carried params results finalL finalR : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {bodyL : Body Op carried sigsL} {bodyR : Body Op carried sigsR}
variable {first current next : Carries m ids σ carried}

/-- Each complete paired outer activation replays as a positive segment,
retaining the parent continuation and the exact carried tuple and store. -/
theorem IterationPair.steps (paired : IterationPair primitives bodyL bodyR first next)
    (parentL : Continuation.Stack m carried finalL) (parentR : Continuation.Stack m carried finalR) :
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsL bodyL (first.left, first.store)).config parentL)
      ((Feedback.Restart.mk carried sigsL bodyL (next.left, next.store)).config parentL) ∧
    TransGen (Step primitives) ((Feedback.Restart.mk carried sigsR bodyR (first.right, first.store)).config parentR)
      ((Feedback.Restart.mk carried sigsR bodyR (next.right, next.store)).config parentR) :=
  Proofs.iteration_steps paired parentL parentR

/-- Every paired outer restart either supplies a completed feedback step
or observes exit, block or productive inner execution. The classical
split constructs a stream only from positive paired feedback witnesses. -/
theorem loop_observations (admitted : Gamma.CodePair Op mapping bodyL bodyR)
    (respects : ActionsRespect primitives ids) (first : Carries m ids σ carried) :
    LoopPair primitives mapping bodyL bodyR first :=
  Proofs.classify admitted respects first

/-- Prepend completed outer activations to the actual final iteration
evaluations on either side, retaining the exact outcomes. -/
theorem IterationPair.replay
    {outcomeL outcomeR : Continuation.Partial.Outcome m σ carried}
    (completed : ReflTransGen (IterationPair primitives bodyL bodyR) first current)
    (later : Eval primitives (.iteration bodyL current.left) current.store outcomeL ∧
      Eval primitives (.iteration bodyR current.right) current.store outcomeR) :
    Eval primitives (.iteration bodyL first.left) first.store outcomeL ∧
    Eval primitives (.iteration bodyR first.right) first.store outcomeR :=
  Proofs.rewind completed later

/-- A productive inner activation reachable by completed outer feedback
excludes an infinite stream of completed outer activations from that same
start. Determinism makes the stream pass through the specified restart. -/
theorem inner_excludes_outer (completed : ReflTransGen (IterationPair primitives bodyL bodyR) first current)
    (inner : Gamma.ProductivePair primitives ids (.region bodyL current.left PUnit.unit)
      (.region bodyR current.right PUnit.unit) current.store) :
    ¬ InfiniteTrace (IterationPair primitives bodyL bodyR) first :=
  Proofs.inner_excludes_outer completed inner

/-- At actual successful dispatch, both productive modes replay to
infinite microsteps in either direction. Finite endpoints are terminal. -/
theorem CallPair.infinite_iff {sourceL sourceR : Config m σ outs}
    (paired : CallPair primitives ids mapping outs sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR :=
  Proofs.infinite_iff paired

/-- Compose ordered partial ω linking with two-level θ body renumbering.
Actual dispatch supplies the selected closures and exact post-link store. -/
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
      ((request unitR right inputR port argsR store).start primitives) :=
  Proofs.link_then_invoke respects iso schedule identities imports port arguments store admitted

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.NestedLoop
