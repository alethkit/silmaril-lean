module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Productivity

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args outs : Ports (Ty V S)} {sigs sigs' : List (Ports (Ty V S))}
variable {a b : Activation m outs}

/-- Both supported call entries have productive runs together. Each reachable
entry must remain in the checked slice on its own side. -/
theorem diverges_iff (respects : PrimitivesRespect m ids) (paired : Activation.Related m ids a b)
    (supportedL : SupportedFrom m a) (supportedR : SupportedFrom m b) :
    Diverges m a ↔ Diverges m b :=
  Proofs.diverges_iff respects paired supportedL supportedR

/-- Typed module renumbering preserves and reflects productive execution from
the actual linked export when the reachable bodies on both sides are supported. -/
theorem exported_diverges_iff (respects : PrimitivesRespect m ids) (unitL unitR : Nat)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {importsL importsR : Tuple m.Val args} (imports : TupleRelated m ids importsL importsR)
    {params results : Ports (Ty V S)} (port : Port outs (.value (.function params results)))
    {inputL inputR : Tuple m.Val params} (inputs : TupleRelated m ids inputL inputR)
    (supportedL : SupportedFrom m (exported m unitL left importsL port inputL))
    (supportedR : SupportedFrom m (exported m unitR right importsR port inputR)) :
    Diverges m (exported m unitL left importsL port inputL) ↔
      Diverges m (exported m unitR right importsR port inputR) :=
  diverges_iff respects
    (.intro ((Recursive.linkGraph_related respects unitL unitR iso allocated imports).get port) inputs)
    supportedL supportedR

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix
