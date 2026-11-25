module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Reflection
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Simulation

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent

open Relation (TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {job : Job m ports} {next : Entry m} {pending : Pending m next.results ports}

/-- Execute the independently specified prefix, including any completed
calls it contains, and stop before opening the selected callee. -/
theorem Prefix.microsteps (reached : Prefix m job next pending) (stack : Stack m ports final) :
    TransGen Step (.eval job stack) (next.state (pending.push stack)) :=
  Proofs.prefix_steps reached stack

/-- A call followed by its prefix reaches the real next callee with
its full argument tuple and the exact suspended binding frames. -/
theorem entry_microsteps {entry : Entry m} {pending : Pending m next.results entry.results}
    (reached : Prefix m entry.openBody next pending) (stack : Stack m entry.results final) :
    TransGen Step (entry.state stack) (next.state (pending.push stack)) :=
  Proofs.entry_steps reached stack

/-- Every descent step retains its predecessor stack and strictly
increases the number of pending continuation frames. -/
theorem Run.stack_grows (run : Run m) (base : Stack m (run.entry 0).results final) (n : Nat) :
    stackDepth (run.stackAt base n) < stackDepth (run.stackAt base (n + 1)) :=
  Proofs.stack_grows run base n

/-- Realize the supplied nested descent on a single infinite execution with
strictly successive positions for all exact call and stack observations. -/
theorem Run.checkpoints (run : Run m) (base : Stack m (run.entry 0).results final) :
    ∃ micro positions, Checkpoints run base micro positions :=
  Proofs.checkpoints run base

theorem Run.infinite (run : Run m) (base : Stack m (run.entry 0).results final) :
    InfiniteTrace Step ((run.entry 0).state base) := by
  obtain ⟨micro, _, trace⟩ := run.checkpoints base
  exact ⟨micro, by simpa only [trace.first, Run.stackAt] using trace.atEntry 0, trace.steps⟩

/-- Recover an independent prefix between actual call entries. The caller
has yet to return, and every call or θ activation begun after entering its
body and before the selected call has returned to its own saved stack.
The resulting pending frames reproduce the observed stack exactly. -/
theorem entry_of_interval {micro : Nat → State m final} {begin finish : Nat}
    (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {stack : Stack m caller.results final} {nextStack : Stack m next.results final}
    (atCaller : micro begin = caller.state stack) (atCallee : micro finish = next.state nextStack)
    (rising : begin < finish) (live : BeforeReturn micro (begin + 1) finish stack)
    (earlier : EarlierJobsReturn micro (begin + 1) finish) :
    ∃ pending, Prefix m caller.openBody next pending ∧ pending.push stack = nextStack :=
  Proofs.entry_of_theta_interval steps atCaller atCallee rising live
    (fun i lower upper {_ _} callee args frame entered => earlier i lower upper (.call callee args) frame entered trivial)

/-- Recover the independent prefix even when θ is still active at the
selected call. The first returns of completed body iterations recover
their carried tuples and feedback selectors. Earlier calls must have
returned before the checkpoint, and the caller remains live. -/
theorem entry_of_theta_interval {micro : Nat → State m final} {begin finish : Nat}
    (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {stack : Stack m caller.results final} {nextStack : Stack m next.results final}
    (atCaller : micro begin = caller.state stack) (atCallee : micro finish = next.state nextStack)
    (rising : begin < finish) (live : BeforeReturn micro (begin + 1) finish stack)
    (earlier : EarlierCallsReturn micro (begin + 1) finish) :
    ∃ pending, Prefix m caller.openBody next pending ∧ pending.push stack = nextStack :=
  Proofs.entry_of_theta_interval steps atCaller atCallee rising live earlier

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent
