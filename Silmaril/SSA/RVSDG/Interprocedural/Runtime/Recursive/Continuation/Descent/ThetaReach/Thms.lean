module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Replay
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Reflection

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {job : Job m ports} {target : Restart m} {pending : Pending m target.carried ports}

/-- Execute a finite independent route up to the selected restart. -/
theorem Reaches.microsteps (reached : Reaches m job target pending) (stack : Stack m ports final) :
    Relation.ReflTransGen Step (.eval job stack) (target.state (pending.push stack)) :=
  Proofs.reaches_steps reached stack

/-- Recover an independent route to the exact observed restart. The
enclosing job remains live through the interval and earlier calls
have returned before the selected restart. -/
theorem reaches_of_interval {micro : Nat → State m final} {begin finish : Nat}
    (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {stack : Stack m ports final} {targetStack : Stack m target.carried final}
    (opened : micro begin = .eval job stack) (selected : micro finish = target.state targetStack)
    (ordered : begin ≤ finish) (live : BeforeReturn micro begin finish stack)
    (earlier : EarlierCallsReturn micro begin finish) :
    ∃ pending, Reaches m job target pending ∧ pending.push stack = targetStack :=
  Proofs.reaches_of_interval steps opened selected ordered live earlier

/-- Stitch the finite call chain and θ route to the productive feedback. -/
theorem FeedbackRoute.infinite {caller : Entry m} {stack : Stack m caller.results final}
    (route : FeedbackRoute m caller stack) : InfiniteTrace Step (caller.state stack) :=
  Proofs.route_infinite route

theorem diverges_sound {entry : Entry m} (certificate : Diverges entry) :
    InfiniteTrace Step (entry.state .halt) :=
  Proofs.diverges_sound certificate

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach
