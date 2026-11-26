module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Simulation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall

open Continuation (Stack)
open Continuation.Partial (Config Primitives Step)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs final : Ports (Ty V S)} {primitives : Primitives m σ}

/-- Open the actual related callable values at their paired ordered code,
with their actual captures and arguments and the original saved stacks. -/
theorem open_related {calleeL calleeR : m.Val (.value (.function args outs))}
    {inputL inputR : Tuple m.Val args} {stackL stackR : Stack m outs final}
    (callees : ValueRelated m ids calleeL calleeR)
    (inputs : TupleRelated m ids inputL inputR)
    (code : ResolvedSchedule Op m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR))
    (frames : Frames m ids final stackL stackR) (store : σ) :
    Live m ids σ final ⟨.eval (Job.openClosure m calleeL inputL) stackL, store⟩
      ⟨.eval (Job.openClosure m calleeR inputR) stackR, store⟩ :=
  Proofs.open_related callees inputs code frames store

theorem DispatchReady.call {calleeL calleeR : m.Val (.value (.function args outs))}
    {inputL inputR : Tuple m.Val args} {stackL stackR : Stack m outs final} {storeL storeR : σ}
    (code : ResolvedSchedule Op m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR)) :
    DispatchReady ⟨.eval (.call calleeL inputL) stackL, storeL⟩ ⟨.eval (.call calleeR inputR) stackR, storeR⟩ := by
  intro _ _ _ _ _ _ _ _ left right
  cases left
  cases right
  exact code

/-- Match the two next scheduled boundaries by finite nonempty segments,
or expose their related terminal observations. The only stuttering skips
a finite syntax prefix of empty γ bindings. At an active call, the local
order premise relates the actual resolved bodies. -/
theorem advance {left right : Config m σ final}
    (actions : ActionsRespect primitives ids) (pair : Live m ids σ final left right)
    (ready : DispatchReady left right) : Advance primitives ids left right :=
  Proofs.advance actions pair ready

/-- Any real first microstep on either side belongs to the matching
segment. Determinism identifies that first step even when the segment
must finish several administrative steps before the next paired control. -/
theorem advance_steps {left right : Config m σ final}
    (progress : Advance primitives ids left right) :
    (∀ firstL, Step primitives left firstL → ∃ nextL nextR,
      ReflTransGen (Step primitives) firstL nextL ∧ TransGen (Step primitives) right nextR ∧
      Live m ids σ final nextL nextR) ∧
    (∀ firstR, Step primitives right firstR → ∃ nextL nextR,
      TransGen (Step primitives) left nextL ∧ ReflTransGen (Step primitives) firstR nextR ∧
      Live m ids σ final nextL nextR) :=
  Proofs.advance_steps progress

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall
