module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Proofs

open CallDescent (Entry Run Checkpoints)
open CallDescent.Extraction (LiveFrom FirstChild NonreturningCallAt)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final}

private structure Point (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (final : Ports (Ty V S)) where
  index : Nat
  entry : Entry m σ
  stack : Stack m entry.call.results final

private def Point.config (point : Point m σ final) : Config m σ final :=
  point.entry.config point.stack

private def Point.root (entry : Entry m σ) : Point m σ entry.call.results :=
  ⟨0, entry, .halt⟩

private def Point.Live (point : Point m σ final) (micro : Nat → Config m σ final) : Prop :=
  micro point.index = point.config ∧ LiveFrom micro point.index point.stack

private def ChildStep (primitives : Primitives m σ) (micro : Nat → Config m σ final)
    (parent child : Point m σ final) : Prop :=
  ∃ pending : Descent.Pending m child.entry.call.results parent.entry.call.results,
    FirstChild primitives parent.entry parent.stack micro parent.index child.index child.entry pending ∧
      pending.push parent.stack = child.stack

private theorem child_live {parent child : Point m σ final} (edge : ChildStep primitives micro parent child) :
    child.Live micro := by
  obtain ⟨pending, observed, frames⟩ := edge
  refine ⟨?_, frames ▸ observed.live⟩
  change micro child.index = child.entry.config child.stack
  rw [← frames]
  exact observed.atEntry

private theorem root_live {entry : Entry m σ} {micro : Nat → Config m σ entry.call.results}
    (steps : ∀ i, Step primitives (micro i) (micro (i + 1))) (initial : micro 0 = entry.config .halt) :
    (Point.root entry).Live micro := by
  refine ⟨initial, ?_⟩
  change LiveFrom micro 0 (.halt : Stack m entry.call.results entry.call.results)
  rintro i _ ⟨value, returned⟩
  have state : micro i = ⟨.returned value .halt, (micro i).store⟩ := by
    change (micro i).control = _ at returned
    rw [← returned]
  have edge := steps i
  rw [state] at edge
  exact _root_.Part.notMem_none _ edge

private theorem prepend_calls {parent child : Point m σ final}
    (path : ReflTransGen (ChildStep primitives micro) parent child)
    (ending : FeedbackRoute primitives child.entry child.stack) : FeedbackRoute primitives parent.entry parent.stack := by
  refine path.head_induction_on (motive := fun p _ => FeedbackRoute primitives p.entry p.stack) ending ?_
  intro current next edge _ suffix
  obtain ⟨_, observed, frames⟩ := edge
  rw [← frames] at suffix
  exact .call observed.reaches suffix

private theorem descent_of_chain {entry : Entry m σ} {micro : Nat → Config m σ entry.call.results}
    (steps : ∀ i, Step primitives (micro i) (micro (i + 1))) (initial : micro 0 = entry.config .halt)
    (chain : InfiniteTrace (ChildStep primitives micro) (Point.root entry)) :
    ∃ (run : Run primitives) (base : Stack m (run.entry 0).call.results entry.call.results) (positions : Nat → Nat),
      run.entry 0 = entry ∧ Checkpoints run base micro positions := by
  classical
  obtain ⟨points, first, edges⟩ := chain
  let pending (n : Nat) := Classical.indefiniteDescription _ (edges n)
  let run : Run primitives :=
    ⟨fun n => (points n).entry, fun n => (pending n).val, fun n => (pending n).property.1.reaches⟩
  let base : Stack m (run.entry 0).call.results entry.call.results := (points 0).stack
  have stack_at (n : Nat) : run.stackAt base n = (points n).stack := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (pending n).val.push (run.stackAt base n) = (points (n + 1)).stack
      rw [ih]
      exact (pending n).property.2
  have live (n : Nat) : (points n).Live micro := by
    cases n with
    | zero => simpa only [first] using root_live steps initial
    | succ n => exact child_live (edges n)
  refine ⟨run, base, fun n => (points n).index, congrArg Point.entry first, congrArg Point.index first,
    steps, fun n => (pending n).property.1.later, ?_⟩
  intro n
  rw [stack_at n]
  exact (live n).1

theorem diverges_complete {entry : Entry m σ} (trace : InfiniteTrace (Step primitives) (entry.config .halt)) :
    Diverges primitives entry := by
  classical
  obtain ⟨micro, initial, steps⟩ := trace
  let reached := ReflTransGen (ChildStep primitives micro) (Point.root entry)
  by_cases finite : ∃ p, reached p ∧ p.Live micro ∧ (∀ i, p.index < i → ¬ NonreturningCallAt micro i)
  · obtain ⟨last, path, live, returns⟩ := finite
    obtain ⟨target, pending, positions, inputs, _, route, observed⟩ :=
      CallDescent.Extraction.reaches_feedback_of_live steps live.1 live.2 returns
    exact .inr (prepend_calls path (.restart route observed.productive))
  · have chain : InfiniteTrace (ChildStep primitives micro) (Point.root entry) := by
      apply InfiniteTrace.coinduct (fun p => reached p ∧ p.Live micro) ?_ ⟨.refl, root_live steps initial⟩
      intro parent live
      have existsChild : ∃ i, parent.index < i ∧ NonreturningCallAt micro i := by
        by_contra none
        exact finite ⟨parent, live.1, live.2, fun i later child => none ⟨i, later, child⟩⟩
      obtain ⟨i, next, pending, observed⟩ :=
        CallDescent.Extraction.first_child steps live.2.1 live.2.2 existsChild
      let child : Point m σ _ := ⟨i, next, pending.push parent.stack⟩
      have edge : ChildStep primitives micro parent child := ⟨pending, observed, rfl⟩
      exact ⟨child, edge, live.1.tail edge, child_live edge⟩
    obtain ⟨run, _, _, start, _⟩ := descent_of_chain steps initial chain
    exact .inl ⟨run, start⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Proofs
