module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Region

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin : Nat}

theorem FeedbackOnStream.productive {target : Feedback.Restart m σ} {parent : Stack m target.carried final}
    {positions : Nat → Nat} {inputs : Nat → Tuple m.Val target.carried × σ}
    (observed : FeedbackOnStream primitives micro target parent positions inputs) :
    Feedback.Run primitives target.body target.input :=
  ⟨inputs, observed.initial, observed.iteration⟩

/-- If a supplied actual infinite run stays in its caller and no later
call remains live, one θ has infinitely many successful feedback
iterations on that same run. The observation records all exact
restart positions, carried tuples, stores and the saved parent stack. -/
theorem feedback_of_live (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {base : Stack m caller.call.results final}
    (entered : micro begin = caller.config base) (live : LiveFrom micro begin base)
    (returns : ∀ i, begin < i → ¬ NonreturningCallAt micro i) :
    HasFeedback primitives micro (begin + 1) :=
  Theta.Proofs.feedback_of_live steps entered live returns

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction
