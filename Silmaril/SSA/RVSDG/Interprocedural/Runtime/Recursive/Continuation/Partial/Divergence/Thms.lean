module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Projection
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Replay

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence

open CallDescent (Entry)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {primitives : Primitives m σ} {entry : Entry m σ}

/-- An independent divergence certificate exists exactly when the
empty-stack invocation has an infinite run of actual partial steps. -/
theorem diverges_iff_infinite :
    Diverges primitives entry ↔ InfiniteTrace (Step primitives) (entry.config .halt) :=
  ⟨Proofs.diverges_sound, Proofs.diverges_complete⟩

/-- The root equivalence for the actual selected export of the total
module linker, with partial primitive actions during invocation. -/
theorem linked_diverges_iff (unitId : Nat) {imports exports : Ports (Ty V S)}
    {sigs : List (Ports (Ty V S))} (graph : Omega Op imports exports sigs) (values : Tuple m.Val imports)
    {params results : Ports (Ty V S)} (port : Port exports (.value (.function params results)))
    (arguments : Tuple m.Val params) (store : σ) :
    Diverges primitives (linkedEntry m unitId graph values port arguments store) ↔
      InfiniteTrace (Step primitives) ⟨start (.call ((Recursive.linkGraph m unitId graph values).get port) arguments), store⟩ :=
  diverges_iff_infinite

/-- A finite selected undefined primitive excludes an independent
divergence certificate for that initial invocation. -/
theorem not_diverges_of_blocked {target : Config m σ entry.call.results}
    (path : Relation.ReflTransGen (Step primitives) (entry.config .halt) target)
    (blocked : target.Blocked primitives) : ¬ Diverges primitives entry :=
  fun certificate => no_infinite_of_reaches_blocked path blocked (diverges_iff_infinite.mp certificate)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence
