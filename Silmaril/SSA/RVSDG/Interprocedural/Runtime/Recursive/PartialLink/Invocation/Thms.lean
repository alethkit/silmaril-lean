module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Composition

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation

open Continuation.Partial (Primitives Config Step)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {results : Ports (Ty V S)}
variable {request : Request m σ results} {primitives : Primitives m σ}

/-- Start with exactly the selected linked callable, the supplied typed
arguments, an empty stack, and the post-link store. -/
theorem start_linked {exports : Tuple m.Val request.exports} {store : σ}
    (linked : request.Links primitives (.linked exports store)) :
    request.start primitives =
      .ok ⟨Continuation.start (.call (exports.get request.port) request.arguments), store⟩ :=
  Proofs.start_linked linked

/-- The exact initializer diagnostic is the error result of dispatch. -/
theorem start_error_iff {failure : Failure m σ} :
    request.start primitives = .error failure ↔ request.Links primitives (.undefined failure) :=
  Proofs.start_error_iff

/-- Exactly one of initialization block, invocation return, invocation
block, and independent invocation divergence holds. This is classical. -/
theorem outcomes : Outcomes request primitives :=
  Proofs.outcomes

/-- A finite return is a path to a halt return after successful dispatch. -/
theorem returns_iff_machine :
    request.Returns primitives ↔
      ∃ source : Config m σ results, request.start primitives = .ok source ∧
        ∃ value finalStore, Relation.ReflTransGen (Step primitives) source ⟨.returned value .halt, finalStore⟩ :=
  Proofs.returns_iff_machine

/-- A finite invocation block reaches a selected undefined primitive after dispatch. -/
theorem blocks_iff_machine :
    request.Blocks primitives ↔
      ∃ source : Config m σ results, request.start primitives = .ok source ∧
        ∃ target, Relation.ReflTransGen (Step primitives) source target ∧ target.Blocked primitives :=
  Proofs.blocks_iff_machine

/-- The independent invocation certificate is equivalent to productive
execution from the actual post-link entry. -/
theorem diverges_iff_machine :
    request.Diverges primitives ↔
      ∃ source : Config m σ results, request.start primitives = .ok source ∧
        InfiniteTrace (Step primitives) source :=
  Proofs.diverges_iff_machine

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation
