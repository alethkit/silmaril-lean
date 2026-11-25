module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Defs

/-! Independent divergence certificates for partially interpreted linked calls. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence

open CallDescent (Entry)
open Descent (Pending)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}

/-- Independent finite descent to a productive θ. Every call prefix and
the final route use successful partial evaluations of completed work. -/
inductive FeedbackRoute (primitives : Primitives m σ) {final : Ports (Ty V S)} :
    (caller : Entry m σ) → Stack m caller.call.results final → Prop where
  | restart {caller : Entry m σ} {stack : Stack m caller.call.results final}
      {target : Feedback.Restart m σ} {pending : Pending m target.carried caller.call.results}
      (reaches : Feedback.Reaches primitives caller.call.openBody caller.store target pending)
      (productive : Feedback.Run primitives target.body target.input) : FeedbackRoute primitives caller stack
  | call {caller child : Entry m σ} {stack : Stack m caller.call.results final}
      {pending : Pending m child.call.results caller.call.results}
      (reaches : CallDescent.Prefix primitives caller.call.openBody caller.store child pending)
      (next : FeedbackRoute primitives child (pending.push stack)) : FeedbackRoute primitives caller stack

/-- Either infinitely many independent call prefixes, or finitely many
followed by an independent route to infinitely many completed θ bodies. -/
def Diverges (primitives : Primitives m σ) (entry : Entry m σ) : Prop :=
  (∃ run : CallDescent.Run primitives, run.entry 0 = entry) ∨ FeedbackRoute primitives entry .halt

/-- Use the existing total linker, including its δ initialization, and
add the ambient store at invocation of the selected typed export. -/
def linkedEntry (m : Machine.{u, v, w} Op) (unitId : Nat) {imports exports : Ports (Ty V S)}
    {sigs : List (Ports (Ty V S))} (graph : Omega Op imports exports sigs)
    (values : Tuple m.Val imports) {params results : Ports (Ty V S)}
    (port : Port exports (.value (.function params results))) (arguments : Tuple m.Val params) (store : σ) :
    Entry m σ :=
  ⟨Descent.Completeness.Global.linkedEntry m unitId graph values port arguments, store⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence
