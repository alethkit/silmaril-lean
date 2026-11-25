module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Linking
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Invocation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args outs outs' : Ports (Ty V S)} {sigs sigs' : List (Ports (Ty V S))}

theorem TupleRelated.get {left right : Tuple m.Val outs} (paired : TupleRelated m ids left right)
    {t : Ty V S} (port : Port outs t) : ValueRelated m ids (left.get port) (right.get port) :=
  Isomorphism.Proofs.get_related paired port

/-- Explicit import wires preserve the provider's related colours, including
repeated reads of an export port. -/
theorem wireImports_related (wires : Wires outs [] args) {left right : Tuple m.Val outs}
    (exports : TupleRelated m ids left right) :
    TupleRelated m ids (wireImports m wires left) (wireImports m wires right) :=
  Isomorphism.Proofs.wireImports_related wires exports

theorem RunRelated.some_left {left : Tuple m.Val outs} {right : Option (Tuple m.Val outs')}
    (paired : RunRelated m ids (some left) right) :
    ∃ output, right = some output ∧ TupleRelated m ids left output := by
  cases paired with | some h => exact ⟨_, rfl, h⟩

theorem RunRelated.some_right {left : Option (Tuple m.Val outs)} {right : Tuple m.Val outs'}
    (paired : RunRelated m ids left (some right)) :
    ∃ output, left = some output ∧ TupleRelated m ids output right := by
  cases paired with | some h => exact ⟨_, rfl, h⟩

/-- The actual linker preserves and reflects successful linking with related
imports and δ identities. The ordered exports carry related values. -/
theorem linkGraph_related (respects : PrimitivesRespect m ids) (unitL unitR : Nat)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {inL inR : Tuple m.Val args} (inputs : TupleRelated m ids inL inR) :
    RunRelated m ids (linkGraph m unitL left inL) (linkGraph m unitR right inR) :=
  Isomorphism.Proofs.link_related respects unitL unitR iso allocated inL inR inputs

theorem linkTerm_related (respects : PrimitivesRespect m ids) (unitL unitR : Nat)
    {left : OmegaTerm Op args outs sigs} {right : OmegaTerm Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.toGraph.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {inL inR : Tuple m.Val args} (inputs : TupleRelated m ids inL inR) :
    RunRelated m ids (linkTerm m unitL left inL) (linkTerm m unitR right inR) := by
  rw [← link_toGraph, ← link_toGraph]
  exact linkGraph_related respects unitL unitR ((left.renumberedBy_toGraph_iff right rename).2 iso) allocated inputs

/-- Related closures match success or exhaustion at each pair of bounds.
A successful return has the same data, state and control observations,
and relates any globals and closures in the returned tuple. -/
theorem invoke_related (respects : PrimitivesRespect m ids) (loops calls : Nat)
    {params results : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function params results))}
    (callees : ValueRelated m ids calleeL calleeR) {inL inR : Tuple m.Val params}
    (inputs : TupleRelated m ids inL inR) :
    RunRelated m ids (invoke m loops calls calleeL inL) (invoke m loops calls calleeR inR) :=
  Isomorphism.Proofs.invoke_related respects loops calls callees inputs

/-- Link each graph and invoke the callable at the same export port. -/
theorem exportedCall_related (respects : PrimitivesRespect m ids) (unitL unitR loops calls : Nat)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {importsL importsR : Tuple m.Val args} (imports : TupleRelated m ids importsL importsR)
    {params results : Ports (Ty V S)} (port : Port outs (.value (.function params results)))
    {inL inR : Tuple m.Val params} (inputs : TupleRelated m ids inL inR) :
    RunRelated m ids
      ((linkGraph m unitL left importsL).bind (fun exports => invoke m loops calls (exports.get port) inL))
      ((linkGraph m unitR right importsR).bind (fun exports => invoke m loops calls (exports.get port) inR)) :=
  Isomorphism.Proofs.bind_related (linkGraph_related respects unitL unitR iso allocated imports)
    (fun _ _ exports => invoke_related respects loops calls (exports.get port) inputs)

/-- Resolve a client's ordered imports from related provider runs, link the
client, and invoke its export at the same typed port on both sides. -/
theorem exportedCall_withImports_related (respects : PrimitivesRespect m ids)
    (unitL unitR loops calls : Nat) {provided : Ports (Ty V S)}
    {providerL providerR : Option (Tuple m.Val provided)} (providers : RunRelated m ids providerL providerR)
    (wires : Wires provided [] args)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {params results : Ports (Ty V S)} (port : Port outs (.value (.function params results)))
    {inL inR : Tuple m.Val params} (inputs : TupleRelated m ids inL inR) :
    RunRelated m ids
      (do
        let providerExports ← providerL
        let exports ← linkGraph m unitL left (wireImports m wires providerExports)
        invoke m loops calls (exports.get port) inL)
      (do
        let providerExports ← providerR
        let exports ← linkGraph m unitR right (wireImports m wires providerExports)
        invoke m loops calls (exports.get port) inR) :=
  Isomorphism.Proofs.bind_related providers (fun _ _ exports =>
    exportedCall_related respects unitL unitR loops calls iso allocated
      (wireImports_related wires exports) port inputs)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime
