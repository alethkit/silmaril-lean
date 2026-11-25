module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Calls
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Proofs

open Continuation.Partial (Primitives)
open PartialLink.Invocation (start_error_iff start_linked)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {unitL unitR : Nat}
variable {args outs params results : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}

theorem link_then_invoke_related (respects : ActionsRespect primitives ids)
    {left : Omega Op args outs sigsL} {right : Omega Op args outs sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Ordered Op (renameVertex positions) args outs left.toTerm.region right.toTerm.region)
    (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputL inputR : Tuple m.Val args} (imports : TupleRelated m ids inputL inputR)
    (port : Port outs (.value (.function params results)))
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR) (store : σ)
    (shared : ∀ {exportsL exportsR : Tuple m.Val outs} {post : σ},
      Links primitives unitL left inputL store (.linked exportsL post) →
      Links primitives unitR right inputR store (.linked exportsR post) →
      SharedLambda m params results (exportsL.get port) (exportsR.get port)) :
    ObservationsRelated primitives ids (renameVertex positions) results
      ((request unitL left inputL port argsL store).start primitives)
      ((request unitR right inputR port argsR store).start primitives) := by
  have paired := link_related respects iso schedule identities imports store
  have linkedL : Links primitives unitL left inputL store (link primitives unitL left inputL store) := link_spec
  have linkedR : Links primitives unitR right inputR store (link primitives unitR right inputR store) := link_spec
  generalize link primitives unitL left inputL store = outcomeL at paired linkedL
  generalize link primitives unitR right inputR store = outcomeR at paired linkedR
  cases paired with
  | undefined address identity site stopped =>
    rw [(start_error_iff (request := request unitL left inputL port argsL store) (primitives := primitives)).mpr linkedL,
      (start_error_iff (request := request unitR right inputR port argsR store) (primitives := primitives)).mpr linkedR]
    exact .linkBlocked address identity site stopped
  | linked exports post =>
    rw [start_linked (request := request unitL left inputL port argsL store) (primitives := primitives) linkedL,
      start_linked (request := request unitR right inputR port argsR store) (primitives := primitives) linkedR]
    exact call_observations respects (exports.get port) (shared linkedL linkedR) arguments post
      (renameVertex positions)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Proofs
