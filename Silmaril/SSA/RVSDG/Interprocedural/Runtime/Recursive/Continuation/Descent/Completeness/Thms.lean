module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Calls

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {final : Ports (Ty V S)}
variable {micro : Nat → State m final} {begin : Nat}

/-- If any later call remains live, extract the first such entry
and its independent prefix, including any finite θ feedback. -/
theorem first_child (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {base : Stack m caller.results final}
    (entered : micro begin = caller.state base) (live : LiveFrom micro begin base)
    (existsChild : ∃ i, begin < i ∧ NonreturningCallAt micro i) :
    HasFirstChild caller base micro begin :=
  Proofs.first_child steps entered live existsChild

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness
