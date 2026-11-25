module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Defs

/-! Rooted certificates on one continuation microstep stream. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {final : Ports (Ty V S)}

structure Point (m : Machine.{u, v, w} Op) (final : Ports (Ty V S)) where
  index : Nat
  entry : Entry m
  stack : Stack m entry.results final

def Point.state (point : Point m final) : State m final :=
  point.entry.state point.stack

def Point.root (entry : Entry m) : Point m entry.results :=
  ⟨0, entry, .halt⟩

def Point.Live (point : Point m final) (micro : Nat → State m final) : Prop :=
  micro point.index = point.state ∧ LiveFrom micro point.index point.stack

/-- One least nonreturning child on this stream with the exact pending
frames supplied by the independent prefix. -/
def ChildStep (micro : Nat → State m final) (parent child : Point m final) : Prop :=
  ∃ pending : Pending m child.entry.results parent.entry.results,
    FirstChild parent.entry parent.stack micro parent.index child.index child.entry pending ∧
      pending.push parent.stack = child.stack

/-- A finite chain of nested calls ends at a live call whose later calls
all return. Its actual stream then reaches productive θ feedback. -/
def FeedbackAfterCalls (entry : Entry m) (micro : Nat → State m entry.results) : Prop :=
  ∃ last, ReflTransGen (ChildStep micro) (Point.root entry) last ∧ last.Live micro ∧
    (∀ i, last.index < i → ¬ NonreturningCallAt micro i) ∧ HasFeedback micro (last.index + 1)

def Classification (entry : Entry m) (micro : Nat → State m entry.results) : Prop :=
  InfiniteTrace (ChildStep micro) (Point.root entry) ∨ FeedbackAfterCalls entry micro

/-- The actual ordered export of the recursive ω linker. -/
def linkedEntry (m : Machine.{u, v, w} Op) (unitId : Nat) {imports exports : Ports (Ty V S)}
    {sigs : List (Ports (Ty V S))} (graph : Omega Op imports exports sigs)
    (values : Tuple m.Val imports) {params results : Ports (Ty V S)}
    (port : Port exports (.value (.function params results))) (arguments : Tuple m.Val params) : Entry m :=
  ⟨results, Tail.exported m unitId graph values port arguments⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global
