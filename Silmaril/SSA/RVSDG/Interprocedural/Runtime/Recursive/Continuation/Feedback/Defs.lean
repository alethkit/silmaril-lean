module

public import Silmaril.Foundations.InfiniteTrace
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Defs

/-! Productive sequences of completed θ body activations. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {carried current final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}

/-- The independent finite judgment supplies the whole next tuple and
a selector that requests feedback. -/
def Iteration (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input next : Tuple m.Val carried) : Prop :=
  ∃ tag, Returns m (.region body input (PUnit.unit : Locals m.Val [])) (.cons tag next) ∧
    (tag.selector.val == 1) = true

def Run (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input : Tuple m.Val carried) : Prop :=
  InfiniteTrace (Iteration body) input

def atReturn (frame : Stack m current final) (state : State m final) : Prop :=
  ∃ value : Tuple m.Val current, state = .returned value frame

/-- Stay within a job's activation by stopping at its first return to
the supplied frame. Nested calls and loops use their ordinary steps. -/
def InsideStep (frame : Stack m current final) (source target : State m final) : Prop :=
  Step source target ∧ ¬ atReturn frame source

/-- The actual θ boundary, with its saved enclosing continuation. -/
def restart (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (input : Tuple m.Val carried) : State m final :=
  .eval (.iteration body input) parent

/-- Between successive restarts, run the body to its first return to
the θ frame and take the actual feedback edge. The entry step from
the restart to a fresh body is fixed by the machine. -/
def Segment (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (input next : Tuple m.Val carried) : Prop :=
  ∃ tag,
    Relation.ReflTransGen (InsideStep (.loop body parent))
      (.eval (.region body input (PUnit.unit : Locals m.Val [])) (.loop body parent))
      (.returned (.cons tag next) (.loop body parent)) ∧
    Step (.returned (.cons tag next) (.loop body parent)) (restart body parent next)

/-- An actual microstep stream indexed at successive restarts of the
same θ activation. Each interval ends with its first body return
to the loop frame and the feedback edge. -/
structure RestartTrace
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (inputs : Nat → Tuple m.Val carried)
    (micro : Nat → State m final) (indices : Nat → Nat) : Prop where
  first : indices 0 = 0
  steps : ∀ i, Step (micro i) (micro (i + 1))
  atRestart : ∀ n, micro (indices n) = restart body parent (inputs n)
  later : ∀ n, indices n + 1 < indices (n + 1)
  bodyReturn : ∀ n, ∃ tag, micro (indices (n + 1) - 1) =
    .returned (.cons tag (inputs (n + 1))) (.loop body parent)
  inside : ∀ n i, indices n < i → i + 1 < indices (n + 1) →
    ¬ atReturn (.loop body parent) (micro i)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback
