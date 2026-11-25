module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Progress
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Trichotomy

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ}

/-- Progress for every typed configuration. The control constructors and
the total resolver suffice, so the theorem applies at every reachable state. -/
theorem Config.progress (source : Config m σ final) :
    (∃ value, source.control = .returned value .halt) ∨ source.Blocked primitives ∨
      ∃ target, Step primitives source target :=
  Classification.Proofs.progress source

/-- The only configurations without a successor are the exact halt
return and a selected primitive with undefined output. -/
theorem Config.no_step_iff (source : Config m σ final) :
    (∀ target, ¬ Step primitives source target) ↔
      (∃ value, source.control = .returned value .halt) ∨ source.Blocked primitives :=
  Classification.Proofs.no_step_iff source

namespace Classification

theorem trichotomy {entry : CallDescent.Entry m σ} : Trichotomy primitives entry :=
  Proofs.trichotomy

/-- Classify the invocation of a selected export after total linking,
including total δ initialization. This is a classical proposition. -/
theorem linked_trichotomy (unitId : Nat) {imports exports : Ports (Ty V S)}
    {sigs : List (Ports (Ty V S))} (graph : Omega Op imports exports sigs)
    (values : Tuple m.Val imports) {params results : Ports (Ty V S)}
    (port : Port exports (.value (.function params results))) (arguments : Tuple m.Val params) (store : σ) :
    Trichotomy primitives (Divergence.linkedEntry m unitId graph values port arguments store) :=
  trichotomy

end Classification

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
