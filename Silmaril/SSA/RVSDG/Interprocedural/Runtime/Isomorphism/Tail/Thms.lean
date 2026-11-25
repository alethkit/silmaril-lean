module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args outs : Ports (Ty V S)} {sigs sigs' : List (Ports (Ty V S))}
variable {a b : Activation m outs}

/-- Corresponding resolutions preserve all three outcomes. Call-entry
outcomes have related target activations, giving a one-step match in both directions. -/
theorem inspect_related (respects : PrimitivesRespect m ids) (paired : Activation.Related m ids a b) :
    Outcome.Related m ids (inspect m a) (inspect m b) :=
  Isomorphism.Proofs.inspect_related respects paired

/-- Match a given stream at the same transition index and with related call entries. -/
theorem stream_right (respects : PrimitivesRespect m ids) (paired : Activation.Related m ids a b)
    (left : Nat → Activation m outs) (initial : left 0 = a) (steps : ∀ n, Step m (left n) (left (n + 1))) :
    ∃ right : Nat → Activation m outs, right 0 = b ∧
      (∀ n, Step m (right n) (right (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  Isomorphism.Proofs.stream_right respects paired left initial steps

theorem stream_left (respects : PrimitivesRespect m ids) (paired : Activation.Related m ids a b)
    (right : Nat → Activation m outs) (initial : right 0 = b) (steps : ∀ n, Step m (right n) (right (n + 1))) :
    ∃ left : Nat → Activation m outs, left 0 = a ∧
      (∀ n, Step m (left n) (left (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  Isomorphism.Proofs.stream_left respects paired right initial steps

/-- Every actual call transition in either run can be matched on the other side. -/
theorem diverges_iff (respects : PrimitivesRespect m ids) (paired : Activation.Related m ids a b) :
    Diverges m a ↔ Diverges m b :=
  Isomorphism.Proofs.diverges_iff respects paired

/-- Start the infinite call machine at the actual export of each recursive linker. -/
theorem exported_diverges_iff (respects : PrimitivesRespect m ids) (unitL unitR : Nat)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {importsL importsR : Tuple m.Val args} (imports : TupleRelated m ids importsL importsR)
    {params results : Ports (Ty V S)} (port : Port outs (.value (.function params results)))
    {inputL inputR : Tuple m.Val params} (inputs : TupleRelated m ids inputL inputR) :
    Diverges m (exported m unitL left importsL port inputL) ↔
      Diverges m (exported m unitR right importsR port inputR) :=
  diverges_iff respects (.intro ((Recursive.linkGraph_related respects unitL unitR iso allocated imports).get port) inputs)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail
