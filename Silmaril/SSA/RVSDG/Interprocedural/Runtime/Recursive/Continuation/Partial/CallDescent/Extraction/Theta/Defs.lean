module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Defs

/-! Successful θ feedback on the supplied partial-machine stream. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}

/-- Every observed iteration restarts the same θ under the same parent.
The independent successful evaluation carries the exact tuple and store. -/
structure FeedbackOnStream (primitives : Primitives m σ) (micro : Nat → Config m σ final)
    (target : Feedback.Restart m σ) (parent : Stack m target.carried final)
    (positions : Nat → Nat) (inputs : Nat → Tuple m.Val target.carried × σ) : Prop where
  initial : inputs 0 = target.input
  live : LiveFrom micro (positions 0) parent
  rising : ∀ n, positions n < positions (n + 1)
  atRestart : ∀ n, micro (positions n) =
    (Feedback.Restart.mk target.carried target.sigs target.body (inputs n)).config parent
  iteration : ∀ n, Feedback.Iteration primitives target.body (inputs n) (inputs (n + 1))

def HasFeedback (primitives : Primitives m σ) (micro : Nat → Config m σ final) (begin : Nat) : Prop :=
  ∃ (target : Feedback.Restart m σ) (parent : Stack m target.carried final) (positions : Nat → Nat)
    (inputs : Nat → Tuple m.Val target.carried × σ),
    begin ≤ positions 0 ∧ FeedbackOnStream primitives micro target parent positions inputs

/-- The independent finite route reaches the observed θ under exactly
the frames left pending on the given stream. -/
def ReachesFeedback (primitives : Primitives m σ) (micro : Nat → Config m σ final) (begin : Nat)
    {ports : Ports (Ty V S)} (job : Job m ports) (store : σ) (stack : Stack m ports final) : Prop :=
  ∃ (target : Feedback.Restart m σ) (pending : Descent.Pending m target.carried ports) (positions : Nat → Nat)
    (inputs : Nat → Tuple m.Val target.carried × σ),
    begin ≤ positions 0 ∧ Feedback.Reaches primitives job store target pending ∧
      FeedbackOnStream primitives micro target (pending.push stack) positions inputs

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction
