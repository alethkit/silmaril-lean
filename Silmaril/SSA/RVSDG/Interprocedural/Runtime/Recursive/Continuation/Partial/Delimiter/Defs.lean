module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs

/-! Partial steps before a job returns to its enclosing frame. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}

/-- Execute within an activation until the first return to its frame. -/
def InsideStep (primitives : Primitives m σ) (frame : Stack m ports final)
    (source target : Config m σ final) : Prop :=
  Step primitives source target ∧ ¬ Continuation.Feedback.atReturn frame source.control

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
