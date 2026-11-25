module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Proofs

open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {final : Ports (Ty V S)}
variable {micro : Nat → State m final} {parent child : Point m final}

theorem child_live (edge : ChildStep micro parent child) : child.Live micro := by
  obtain ⟨pending, observed, stack⟩ := edge
  refine ⟨?_, stack ▸ observed.live⟩
  change micro child.index = child.entry.state child.stack
  rw [← stack]
  exact observed.atEntry

theorem child_grows (edge : ChildStep micro parent child) :
    parent.index < child.index ∧ stackDepth parent.stack < stackDepth child.stack := by
  obtain ⟨pending, observed, stack⟩ := edge
  exact ⟨observed.later, stack ▸ observed.deeper⟩

theorem path_grows (path : TransGen (ChildStep micro) parent child) :
    parent.index < child.index ∧ stackDepth parent.stack < stackDepth child.stack := by
  induction path with
  | single edge => exact child_grows edge
  | tail _ edge ih =>
    have next := child_grows edge
    exact ⟨ih.1.trans next.1, ih.2.trans next.2⟩

private theorem root_live {entry : Entry m} {micro : Nat → State m entry.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (initial : micro 0 = entry.state .halt) :
    (Point.root entry).Live micro := by
  refine ⟨initial, ?_⟩
  rintro i _ ⟨_, returned⟩
  have edge := steps i
  rw [returned] at edge
  cases edge

theorem classify_root {entry : Entry m} {micro : Nat → State m entry.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (initial : micro 0 = entry.state .halt) :
    Classification entry micro := by
  classical
  by_cases finite : FeedbackAfterCalls entry micro
  · exact .inr finite
  · left
    let reached := ReflTransGen (ChildStep micro) (Point.root entry)
    apply InfiniteTrace.coinduct (fun p => reached p ∧ p.Live micro) ?_
      ⟨.refl, root_live steps initial⟩
    intro parent hp
    rcases split_live steps hp.2.1 hp.2.2 with ⟨i, entry, pending, observed⟩ | feedback
    · let child : Point m _ := ⟨i, entry, pending.push parent.stack⟩
      have edge : ChildStep micro parent child := ⟨pending, observed, rfl⟩
      exact ⟨child, edge, hp.1.tail edge, child_live edge⟩
    · exact False.elim (finite ⟨parent, hp.1, hp.2, feedback⟩)

theorem chain_checkpoints {entry : Entry m} {micro : Nat → State m entry.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (initial : micro 0 = entry.state .halt)
    (chain : InfiniteTrace (ChildStep micro) (Point.root entry)) :
    ∃ (run : Run m) (base : Stack m (run.entry 0).results entry.results) (positions : Nat → Nat),
      (run.entry 0).state base = entry.state .halt ∧ Checkpoints run base micro positions := by
  classical
  obtain ⟨points, first, edges⟩ := chain
  let pending (n : Nat) := Classical.indefiniteDescription _ (edges n)
  let run : Run m := ⟨fun n => (points n).entry, fun n => (pending n).val, fun n => (pending n).property.1.reaches⟩
  let base : Stack m (run.entry 0).results entry.results := (points 0).stack
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
  refine ⟨run, base, fun n => (points n).index, congrArg Point.state first, congrArg Point.index first,
    steps, fun n => (child_grows (edges n)).1, ?_⟩
  intro n
  rw [stack_at n]
  exact (live n).1

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Proofs
