module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Linking

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism

open Continuation.Partial (Primitives)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {unitL unitR : Nat} {args outs : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}

/-- A typed ω renumbering with aligned initializer order preserves the
actual link observation. Success relates ordered exports, including global
identities and callable references at corresponding fixed φ member slots.
Failure matches the first undefined δ, the selected typed primitive and
operands, and the exact attempt store. -/
theorem link_related (respects : ActionsRespect primitives ids)
    {left : Omega Op args outs sigsL} {right : Omega Op args outs sigsR}
    {positions : Fin sigsL.length ≃ Fin sigsR.length} (iso : left.RenumberedBy right positions)
    (schedule : Ordered Op (renameVertex positions) args outs left.toTerm.region right.toTerm.region)
    (identities : ∀ i, ids (unitL, i) (unitR, renameVertex positions i))
    {inputL inputR : Tuple m.Val args} (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    OutcomesRelated m ids σ (renameVertex positions) outs
      (link primitives unitL left inputL store) (link primitives unitR right inputR store) :=
  Proofs.link_related respects iso schedule identities inputs store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism
