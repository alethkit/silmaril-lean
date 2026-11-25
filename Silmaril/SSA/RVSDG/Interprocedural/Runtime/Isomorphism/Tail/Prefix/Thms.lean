module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Productivity
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.CallEntries

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args outs : Ports (Ty V S)} {sigs sigs' : List (Ports (Ty V S))}
variable {a b a' b' : Activation m outs}

/-- Admitted exposures of typed-isomorphic regions agree. The two schedules
may permute independent primitives. Each selected path must be admitted under
its own numbering. -/
theorem expose_related (respects : PrimitivesRespect m ids)
    {args' outs' : Ports (Ty V S)}
    {left : NestedTheta.Graph (Instruction Op) args [] sigs outs}
    {right : NestedTheta.Graph (Instruction Op) args' [] sigs' outs'}
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left right)
    (inputL : Tuple m.Val args) (inputR : Tuple m.Val args')
    (inputs : TupleRelated m ids inputL inputR)
    (safeL : expose m left inputL ≠ .unsupported) (safeR : expose m right inputR ≠ .unsupported) :
    Outcome.Related m ids (expose m left inputL) (expose m right inputR) :=
  Proofs.expose_related respects iso inputL inputR inputs safeL safeR

/-- Resolving related closures or fixed φ slots preserves each supported
outcome, including the next callee and its full argument tuple. -/
theorem inspect_related (respects : PrimitivesRespect m ids) (paired : Activation.Related m ids a b)
    (safeL : inspect m a ≠ .unsupported) (safeR : inspect m b ≠ .unsupported) :
    Outcome.Related m ids (inspect m a) (inspect m b) :=
  Proofs.inspect_related respects paired safeL safeR

/-- A source edge witnesses support on that side. Only the receiving side
needs a separate support premise. -/
theorem step_match_right (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (safe : inspect m b ≠ .unsupported)
    (edge : Step m a a') : ∃ b', Step m b b' ∧ Activation.Related m ids a' b' :=
  Proofs.step_match_right respects paired safe edge

theorem step_match_left (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (safe : inspect m a ≠ .unsupported)
    (edge : Step m b b') : ∃ a', Step m a a' ∧ Activation.Related m ids a' b' :=
  Proofs.step_match_left respects paired safe edge

/-- Match every index of a given stream. Support on the receiving side is
required on its reachable activations. -/
theorem stream_match_right (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (supported : SupportedFrom m b)
    (left : Nat → Activation m outs) (initial : left 0 = a) (edges : ∀ n, Step m (left n) (left (n + 1))) :
    ∃ right : Nat → Activation m outs, right 0 = b ∧
      (∀ n, Step m (right n) (right (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  Proofs.stream_match_right respects paired supported left initial edges

theorem stream_match_left (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (supported : SupportedFrom m a)
    (right : Nat → Activation m outs) (initial : right 0 = b) (edges : ∀ n, Step m (right n) (right (n + 1))) :
    ∃ left : Nat → Activation m outs, left 0 = a ∧
      (∀ n, Step m (left n) (left (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  Proofs.stream_match_left respects paired supported right initial edges

/-- Related actual linked exports are suitable sources for the indexed
stream theorems. Fixed φ slots and global allocation identities use the
recursive linker's existing value relation. -/
theorem exported_related (respects : PrimitivesRespect m ids) (unitL unitR : Nat)
    {left : Omega Op args outs sigs} {right : Omega Op args outs sigs'}
    {rename : Fin sigs.length ≃ Fin sigs'.length} (iso : left.RenumberedBy right rename)
    (allocated : ∀ i, Allocates (left.region.vertices i) → ids (unitL, i.val) (unitR, (rename i).val))
    {importsL importsR : Tuple m.Val args} (imports : TupleRelated m ids importsL importsR)
    {params results : Ports (Ty V S)} (port : Port outs (.value (.function params results)))
    {inputL inputR : Tuple m.Val params} (inputs : TupleRelated m ids inputL inputR) :
    Activation.Related m ids (exported m unitL left importsL port inputL)
      (exported m unitR right importsR port inputR) :=
  .intro ((Recursive.linkGraph_related respects unitL unitR iso allocated imports).get port) inputs

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
    (exported_related respects unitL unitR iso allocated imports port inputs) supportedL supportedR

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix
