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

/-- If an earlier job returns and a later job remains live, the
earlier job returns to its own frame before the later entry. -/
theorem return_before_live {other : Ports (Ty V S)} {micro : Nat → Config m σ final}
    {begin finish : Nat} {job : Job m ports} {next : Job m other}
    {frame : Stack m ports final} {child : Stack m other final}
    (steps : ∀ i, Step primitives (micro i) (micro (i + 1))) (ordered : begin < finish)
    (entered : (micro begin).control = .eval job frame) (selected : (micro finish).control = .eval next child)
    (lives : ∀ i, finish ≤ i → ¬ Continuation.Feedback.atReturn child (micro i).control)
    (returns : ∃ i, begin < i ∧ Continuation.Feedback.atReturn frame (micro i).control) :
    ∃ i, begin < i ∧ i < finish ∧ Continuation.Feedback.atReturn frame (micro i).control :=
  Delimiter.Proofs.return_before_live steps ordered entered selected lives returns

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
