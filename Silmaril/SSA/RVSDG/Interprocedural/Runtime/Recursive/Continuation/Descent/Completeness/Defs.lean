module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Defs

/-! Actual call and θ observations in a delimited infinite execution. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}

/-- The execution never reaches a return to this exact saved frame. -/
def LiveFrom (micro : Nat → State m final) (begin : Nat) (frame : Stack m ports final) : Prop :=
  ∀ i, begin ≤ i → ¬ Feedback.atReturn frame (micro i)

def NonreturningCallAt (micro : Nat → State m final) (i : Nat) : Prop :=
  ∃ (entry : Entry m) (frame : Stack m entry.results final),
    micro i = entry.state frame ∧ LiveFrom micro i frame

/-- The first deeper call that remains live on the supplied stream. The
independent prefix determines its exact arguments and saved frames.
Earlier calls have already returned by this entry. -/
structure FirstChild (caller : Entry m) (base : Stack m caller.results final)
    (micro : Nat → State m final) (begin finish : Nat) (child : Entry m)
    (pending : Pending m child.results caller.results) : Prop where
  later : begin < finish
  atEntry : micro finish = child.state (pending.push base)
  live : LiveFrom micro finish (pending.push base)
  earlier : EarlierCallsReturn micro (begin + 1) finish
  reaches : Prefix m caller.openBody child pending

def HasFirstChild (caller : Entry m) (base : Stack m caller.results final)
    (micro : Nat → State m final) (begin : Nat) : Prop :=
  ∃ finish child pending, FirstChild caller base micro begin finish child pending

/-- A finite position on the supplied stream begins infinitely many
completed feedback iterations under the same live loop continuation. -/
def HasFeedback (micro : Nat → State m final) (begin : Nat) : Prop :=
  ∃ (i : Nat) (carried : Ports (Ty V S)) (sigs : List (Ports (Ty V S)))
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (inputs : Nat → Tuple m.Val carried) (positions : Nat → Nat),
    begin ≤ i ∧ LiveFrom micro i parent ∧
      Feedback.RestartTrace body parent inputs (fun n => micro (i + n)) positions

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness
