module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Defs

/-! Decomposing infinite execution within one θ activation. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {carried final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}

abbrev Checkpoint (m : Machine.{u, v, w} Op) (carried : Ports (Ty V S)) := Nat × Tuple m.Val carried

/-- Only feedback is permitted at the selected frame. Returns to other
frames, including nested loops and calls, are unrestricted. -/
def StaysInLoop (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (micro : Nat → State m final) : Prop :=
  ∀ i tag values, micro i = .returned (.cons tag values) (.loop body parent) →
    (tag.selector.val == 1) = true

/-- Positions of the next restart and the first body return preceding it. -/
structure Interval (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (micro : Nat → State m final)
    (first last : Checkpoint m carried) : Prop where
  atStart : micro first.1 = restart body parent first.2
  atNext : micro last.1 = restart body parent last.2
  later : first.1 + 1 < last.1
  bodyReturn : ∃ tag, micro (last.1 - 1) = .returned (.cons tag last.2) (.loop body parent)
  inside : ∀ i, first.1 < i → i + 1 < last.1 → ¬ atReturn (.loop body parent) (micro i)

/-- The next body begins at the given restart and never returns to its
enclosing θ frame. The caller supplies the actual infinite microsteps. -/
def BodyForever (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (micro : Nat → State m final) (point : Checkpoint m carried) : Prop :=
  micro point.1 = restart body parent point.2 ∧
    ∀ i, point.1 < i → ¬ atReturn (.loop body parent) (micro i)

/-- The alternatives refer to the supplied execution and its exact carried
tuples. A reflexive prefix allows divergence in the first body. -/
def Decomposes (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (input : Tuple m.Val carried) (micro : Nat → State m final) : Prop :=
  (∃ inputs indices, inputs 0 = input ∧ RestartTrace body parent inputs micro indices) ∨
    ∃ last, Relation.ReflTransGen (Interval body parent micro) (0, input) last ∧
      BodyForever body parent micro last

/-- Insert the machine's entry step before a stream already at the freshly
entered body with its loop frame. Original microstep i moves to i + 1. -/
def withEntry (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (input : Tuple m.Val carried) (micro : Nat → State m final) :
    Nat → State m final
  | 0 => restart body parent input
  | i + 1 => micro i

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence
