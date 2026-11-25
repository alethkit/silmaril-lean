module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Dispatch

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma

open Continuation.Partial
open Isomorphism.Invocation (request)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs entry returned params results finalL finalR : Ports (Ty V S)} {extra : Nat}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
variable {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
variable {inputL inputR : Tuple m.Val args} {store : σ}
variable {locL locR : Location} {stopL stopR : Block m σ outs}

/-- A block keeps the chosen γ arm positions, mapped local address, typed
operands of the same primitive, and exact attempt store. -/
theorem BlockPair.observations
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    locR = locL.rename mapping ∧ SitesRelated m ids stopL.site stopR.site ∧ stopL.store = stopR.store :=
  Proofs.block_observations stopped

/-- The address certificate erases to the actual independent evaluations,
with each enclosing γ continuation and θ frame retained. -/
theorem BlockPair.evals
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    Eval primitives (.region left inputL PUnit.unit) store stopL.outcome ∧
    Eval primitives (.region right inputR PUnit.unit) store stopR.outcome :=
  Proofs.block_evals stopped

/-- γ congruence for paired ordered behaviors. Only the common selected
arm is evaluated. On return the suffix reads the related results. On block
or productive feedback it remains pending in each real machine. -/
theorem gamma
    {childSigsL childSigsR : Fin (extra + 2) → List (Ports (Ty V S))}
    {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsL i) returned}
    {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsR i) returned}
    (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
    (arms : ∀ tag {nextL nextR : Tuple m.Val entry}, TupleRelated m ids nextL nextR →
      RegionPair primitives ids (mapping.child 0 tag.val) (armsL tag) (armsR tag) nextL nextR store)
    (related : TupleRelated m ids inputL inputR) :
    RegionPair primitives ids mapping (code inputs armsL outputs) (code inputs armsR outputs) inputL inputR store :=
  Proofs.gamma inputs outputs arms related

theorem regions (admitted : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping left right inputL inputR store :=
  Proofs.regions admitted respects inputs store

/-- Each side replays the finite route to the common paired feedback
stream, then positive restart segments with its own saved frame. -/
theorem ProductivePair.infinite {jobL jobR : Job m outs}
    (run : ProductivePair primitives ids jobL jobR store)
    (frameL : Continuation.Stack m outs finalL) (frameR : Continuation.Stack m outs finalR) :
    InfiniteTrace (Step primitives) ⟨.eval jobL frameL, store⟩ ∧
    InfiniteTrace (Step primitives) ⟨.eval jobR frameR, store⟩ :=
  Proofs.productive_infinite run frameL frameR

/-- At actual successful dispatch, infinite microsteps transport in
both directions. Finite returns and selected blocks are terminal. -/
theorem CallPair.infinite_iff {sourceL sourceR : Config m σ outs}
    (paired : CallPair primitives ids mapping outs sourceL sourceR) :
    InfiniteTrace (Step primitives) sourceL ↔ InfiniteTrace (Step primitives) sourceR :=
  Proofs.infinite_iff paired

/-- Compose ordered partial ω linking and γ congruence for actual export
dispatch. Terminal observations reflect back to the paired endpoints. -/
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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma
