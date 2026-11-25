module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Iterations
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Dispatch

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta

open Continuation.Partial
open Isomorphism.Invocation (request)
open Relation (TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {rename : Renaming}
variable {args outs carried params results : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {bodyL : Body Op carried sigsL} {bodyR : Body Op carried sigsR}

/-- The paired iteration replays as positive segments on both actual
machines, keeping the saved suffix and the exact restart inputs. -/
theorem FeedbackPair.steps {input next : Carries m ids σ carried}
    (paired : FeedbackPair primitives bodyL bodyR input next)
    (outputs : Wires args [carried] results) (entryL entryR : Tuple m.Val args) :
    TransGen (Step primitives) (restart bodyL outputs entryL (input.left, input.store))
      (restart bodyL outputs entryL (next.left, next.store)) ∧
    TransGen (Step primitives) (restart bodyR outputs entryR (input.right, input.store))
      (restart bodyR outputs entryR (next.right, next.store)) :=
  Proofs.feedback_steps paired outputs entryL entryR

/-- Aligned acyclic activations exit together or hit a mapped block after
a finite prefix, or supply a common infinite sequence of completed feedback
iterations. The constructive successor of every live restart comes from
actual acyclic evaluation. The split and stream extraction use choice. -/
theorem loop_observations (admitted : OrderedGraph rename bodyL bodyR)
    (respects : ActionsRespect primitives ids) (input : Carries m ids σ carried) :
    (∃ outL outR, Finishes primitives rename bodyL bodyR input outL outR) ∨
      InfiniteTrace (FeedbackPair primitives bodyL bodyR) input :=
  Proofs.classify admitted respects input

/-- A terminal activation and its paired feedback prefix replay into
finite evaluations of the actual θ iteration jobs. -/
theorem Finishes.eval {input : Carries m ids σ carried}
    {outcomeL outcomeR : Continuation.Partial.Outcome m σ carried}
    (done : Finishes primitives rename bodyL bodyR input outcomeL outcomeR) :
    Eval primitives (.iteration (embed bodyL.toTerm) input.left) input.store outcomeL ∧
    Eval primitives (.iteration (embed bodyR.toTerm) input.right) input.store outcomeR :=
  Proofs.evaluates done

/-- Invoke the actual closures. Both finite outcomes retain exact stores,
and all terminal observations reflect back into the paired endpoints. -/
theorem calls (respects : ActionsRespect primitives ids)
    {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ScheduledLambda m ids rename params results calleeL calleeR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ) :
    CallPair primitives ids rename results
      ⟨Continuation.start (.call calleeL argsL), store⟩
      ⟨Continuation.start (.call calleeR argsR), store⟩ :=
  Proofs.calls respects callees arguments store

/-- At successful dispatch, genuine infinite microstep execution transports
in both directions by paired positive feedback. A finite block or return
rules out such an execution by determinism. -/
theorem CallPair.infinite_iff {sourceL sourceR : Config m σ results}
    (related : CallPair primitives ids rename results sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR :=
  Proofs.infinite_iff related

/-- Compose ordered partial linking with the single-θ body renumbering.
Actual dispatch uses the linked closures and the exact post-link store. -/
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
      ((request unitR right inputR port argsR store).start primitives) :=
  Proofs.link_then_invoke respects iso schedule identities imports port arguments store admitted

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta
