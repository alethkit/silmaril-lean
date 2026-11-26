module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Runs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall

open Continuation.Partial (Config Primitives Step)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs final : Ports (Ty V S)} {family familyL familyR : Family m} {primitives : Primitives m σ}
variable {a b : Config m σ final}

/-- Membership of every live value persists along the real machine,
including after resolving a call, saving a frame or binding a return. -/
theorem Closed.steps (closed : Closed primitives family) (initial : StateIn family a.control)
    (path : ReflTransGen (Step primitives) a b) : StateIn family b.control :=
  ClosedFamilyProofs.closed_steps closed initial path

/-- Start from related exports and explicit arguments in the supported
families. The root uses the machine's empty continuation. -/
theorem Admitted.call {calleeL calleeR : m.Val (.value (.function args outs))}
    {inputL inputR : Tuple m.Val args} (callees : ValueRelated m ids calleeL calleeR)
    (inputs : TupleRelated m ids inputL inputR)
    (admitL : familyL calleeL) (admitR : familyR calleeR)
    (argsL : TupleIn familyL inputL) (argsR : TupleIn familyR inputR) (store : σ) :
    Admitted m ids familyL familyR ⟨Continuation.start (.call calleeL inputL), store⟩
      ⟨Continuation.start (.call calleeR inputR), store⟩ :=
  ⟨.call store callees inputs .halt, ⟨⟨admitL, argsL⟩, trivial⟩, ⟨⟨admitR, argsR⟩, trivial⟩⟩

namespace ClosedFamily

/-- At every paired boundary the current value membership establishes the
local dispatch premise. -/
theorem dispatch_ready (closed : ClosedFamily primitives ids familyL familyR)
    (pair : Admitted m ids familyL familyR a b) : DispatchReady a b :=
  ClosedFamilyProofs.dispatch_ready closed pair

/-- Another pair of positive segments retains the same closed family at
both endpoints. Otherwise the paired boundary is terminal. -/
theorem progress (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∃ a' b', TransGen (Step primitives) a a' ∧ TransGen (Step primitives) b b' ∧
      Admitted m ids familyL familyR a' b') ∨
    (Advance primitives ids a b ∧ ∀ target, ¬ Step primitives a target) :=
  ClosedFamilyProofs.one_or_terminal actions closed pair

/-- Compose positive paired segments until both machines reach related
terminal configurations, or construct genuinely infinite microstep runs.
The case split is classical. -/
theorem paired_runs (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∃ endL endR, ReachedTerminal primitives ids a b endL endR) ∨
      (InfiniteTrace (Step primitives) a ∧ InfiniteTrace (Step primitives) b) :=
  ClosedFamilyProofs.paired_runs actions closed pair

/-- An exact return on either side is matched by a related typed tuple
and the same final store. -/
theorem returns (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∀ endL valueL store, ReflTransGen (Step primitives) a endL → endL.result = some (valueL, store) →
      ∃ endR valueR, ReflTransGen (Step primitives) b endR ∧ endR.result = some (valueR, store) ∧
        TupleRelated m ids valueL valueR) ∧
    (∀ endR valueR store, ReflTransGen (Step primitives) b endR → endR.result = some (valueR, store) →
      ∃ endL valueL, ReflTransGen (Step primitives) a endL ∧ endL.result = some (valueL, store) ∧
        TupleRelated m ids valueL valueR) :=
  ClosedFamilyProofs.returns actions closed pair

/-- A block on either side identifies the paired undefined attempts via
`ReachedTerminal` and its `Advance.blocked` evidence. The evidence
contains typed operands, exact store and corresponding saved frames. -/
theorem blocks (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∀ endL, ReflTransGen (Step primitives) a endL → endL.Blocked primitives →
      ∃ endR, ReachedTerminal primitives ids a b endL endR ∧ endR.Blocked primitives) ∧
    (∀ endR, ReflTransGen (Step primitives) b endR → endR.Blocked primitives →
      ∃ endL, ReachedTerminal primitives ids a b endL endR ∧ endL.Blocked primitives) :=
  ClosedFamilyProofs.blocks actions closed pair

theorem infinite_iff (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    InfiniteTrace (Step primitives) a ↔ InfiniteTrace (Step primitives) b :=
  ClosedFamilyProofs.infinite_iff actions closed pair

end ClosedFamily

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall
