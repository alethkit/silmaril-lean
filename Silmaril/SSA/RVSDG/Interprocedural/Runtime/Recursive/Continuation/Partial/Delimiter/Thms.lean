module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Reflection

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ}

/-- Reflect a first return to the frame of any typed subjob, with the
exact output tuple and store at the return. -/
theorem returns_of_delimited (frame : Stack m ports final) {job : Job m ports} {store finalStore : σ}
    {value : Tuple m.Val ports}
    (path : Relation.ReflTransGen (InsideStep primitives frame) ⟨.eval job frame, store⟩
      ⟨.returned value frame, finalStore⟩) : Eval primitives job store (.returned value finalStore) :=
  Delimiter.Proofs.returns_of_delimited frame path

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
