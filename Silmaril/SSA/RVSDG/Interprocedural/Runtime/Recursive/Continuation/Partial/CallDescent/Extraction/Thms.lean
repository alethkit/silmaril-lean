module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Calls

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin : Nat}

/-- Extract the least later entry whose frame remains live on this actual
infinite partial-machine stream. Earlier calls supply first-return
checkpoints, and finite reflection recovers the independent prefix
with the exact observed store, callable, arguments and pending stack. -/
theorem first_child (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {base : Stack m caller.call.results final}
    (entered : micro begin = caller.config base) (live : LiveFrom micro begin base)
    (existsChild : ∃ i, begin < i ∧ NonreturningCallAt micro i) :
    HasFirstChild primitives caller base micro begin :=
  Proofs.first_child steps entered live existsChild

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction
