module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Calls
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Loops

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {micro : Nat → State m final} {begin : Nat}

/-- A job observed at an evaluation state either returns later to its
saved frame or stays live there on this stream. -/
theorem return_or_live {job : Job m ports} {frame : Stack m ports final}
    (entered : micro begin = .eval job frame) :
    (∃ stop, begin < stop ∧ Feedback.atReturn frame (micro stop)) ∨ LiveFrom micro begin frame :=
  Proofs.return_or_live entered

/-- Finite adequacy and progress delimit any supplied infinite trace
whose starting job has no independent finite return. -/
theorem live_of_no_return (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {job : Job m ports} {frame : Stack m ports final}
    (entered : micro begin = .eval job frame) (noReturn : ∀ value, ¬ Returns m job value) :
    LiveFrom micro begin frame :=
  Proofs.live_of_no_return steps entered noReturn

/-- If any later call remains live, extract the first such entry
and its independent prefix, including any finite θ feedback. -/
theorem first_child (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {base : Stack m caller.results final}
    (entered : micro begin = caller.state base) (live : LiveFrom micro begin base)
    (existsChild : ∃ i, begin < i ∧ NonreturningCallAt micro i) :
    HasFirstChild caller base micro begin :=
  Proofs.first_child steps entered live existsChild

theorem FirstChild.deeper {caller child : Entry m} {base : Stack m caller.results final}
    {finish : Nat} {pending : Pending m child.results caller.results}
    (observed : FirstChild caller base micro begin finish child pending) :
    stackDepth base < stackDepth (pending.push base) :=
  entry_stack_grows observed.reaches base

/-- An actual infinite stream in a live activation has a first deeper
nonreturning call or reaches productive θ feedback with no later
nonreturning call. The current machine interprets primitives as total
single-step tuple transformations, and γ selects one finite child. -/
theorem split_live (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {base : Stack m caller.results final}
    (entered : micro begin = caller.state base) (live : LiveFrom micro begin base) :
    HasFirstChild caller base micro begin ∨
      (∀ i, begin < i → ¬ NonreturningCallAt micro i) ∧ HasFeedback micro (begin + 1) :=
  Proofs.split_live steps entered live

/-- At an exported call started with the empty stack, the infinite
steps themselves imply liveness of the root. -/
theorem split_start {caller : Entry m} {micro : Nat → State m caller.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (entered : micro 0 = caller.state .halt) :
    HasFirstChild caller .halt micro 0 ∨
      (∀ i, 0 < i → ¬ NonreturningCallAt micro i) ∧ HasFeedback micro 1 :=
  Proofs.split_start steps entered

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness
