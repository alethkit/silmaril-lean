module

public import Mathlib.Data.Nat.Find
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Proofs

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {carried final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {parent : Stack m carried final} {input : Tuple m.Val carried}
variable {micro : Nat → State m final}

private theorem no_return_at_restart (values : Tuple m.Val carried) :
    ¬ atReturn (.loop body parent) (restart body parent values) := by
  rintro ⟨_, same⟩
  cases same

private theorem feedback_only {tag : m.Val (.control 2)} {values next : Tuple m.Val carried}
    (edge : Step (.returned (.cons tag values) (.loop body parent)) (restart body parent next)) :
    (tag.selector.val == 1) = true := by
  by_contra stops
  change some (State.finishLoop body tag values parent) = some (restart body parent next) at edge
  rw [State.finishLoop, ite_eq_right stops] at edge
  cases edge

private theorem first_return (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (stays : StaysInLoop body parent micro) (point : Checkpoint m carried)
    (atStart : micro point.1 = restart body parent point.2) :
    BodyForever body parent micro point ∨ ∃ next, Interval body parent micro point next := by
  classical
  let first := point.1 + 1
  by_cases hasReturn : ∃ offset, atReturn (.loop body parent) (micro (first + offset))
  · let offset := Nat.find hasReturn
    obtain ⟨returned, found⟩ := Nat.find_spec hasReturn
    cases returned with
    | cons tag values =>
      let stop := first + offset
      have returnedAt : micro stop = .returned (.cons tag values) (.loop body parent) := found
      have again := stays stop tag values returnedAt
      have feeds : Step (.returned (.cons tag values) (.loop body parent)) (restart body parent values) := by
        change some (State.finishLoop body tag values parent) = some (restart body parent values)
        rw [State.finishLoop, ite_eq_left again]
        rfl
      have atNext : micro (stop + 1) = restart body parent values :=
        step_deterministic (returnedAt ▸ steps stop) feeds
      refine .inr ⟨(stop + 1, values), atStart, atNext, ?_, ⟨tag, ?_⟩, ?_⟩
      · change point.1 + 1 < first + offset + 1
        dsimp [first]
        omega
      · simpa only [Nat.add_sub_cancel] using returnedAt
      · intro i later earlier
        change i + 1 < stop + 1 at earlier
        have afterEntry : first ≤ i := by dsimp [first]; omega
        have smaller : i - first < offset := by dsimp [stop] at earlier; omega
        have guarded := Nat.find_min hasReturn smaller
        simpa only [Nat.add_sub_of_le afterEntry] using guarded
  · refine .inl ⟨atStart, fun i later returned => hasReturn ⟨i - first, ?_⟩⟩
    have afterEntry : first ≤ i := by dsimp [first]; omega
    simpa only [Nat.add_sub_of_le afterEntry] using returned

private theorem at_prefix_end (initial : micro 0 = restart body parent input)
    {last : Checkpoint m carried}
    (path : ReflTransGen (Interval body parent micro) (0, input) last) :
    micro last.1 = restart body parent last.2 := by
  cases path with
  | refl => exact initial
  | tail _ edge => exact edge.atNext

theorem decompose (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (initial : micro 0 = restart body parent input) (stays : StaysInLoop body parent micro) :
    Decomposes body parent input micro := by
  classical
  let starts : Checkpoint m carried := (0, input)
  let reachable := ReflTransGen (Interval body parent micro) starts
  by_cases finite : ∃ last, reachable last ∧ BodyForever body parent micro last
  · exact .inr finite
  · have infinite : InfiniteTrace (Interval body parent micro) starts := by
      apply InfiniteTrace.coinduct reachable ?_ .refl
      intro point reached
      rcases first_return steps stays point (at_prefix_end initial reached) with bodyRun | ⟨next, edge⟩
      · exact False.elim (finite ⟨point, reached, bodyRun⟩)
      · exact ⟨next, edge, reached.tail edge⟩
    obtain ⟨points, first, edges⟩ := infinite
    exact .inl ⟨fun n => (points n).2, fun n => (points n).1, congrArg Prod.snd first,
      congrArg Prod.fst first, steps, fun n => (edges n).atStart, fun n => (edges n).later,
      fun n => (edges n).bodyReturn, fun n => (edges n).inside⟩

private theorem interval_stays {first last : Checkpoint m carried}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (edge : Interval body parent micro first last)
    (i : Nat) (lower : first.1 ≤ i) (upper : i < last.1)
    (tag : m.Val (.control 2)) (values : Tuple m.Val carried)
    (returned : micro i = .returned (.cons tag values) (.loop body parent)) :
    (tag.selector.val == 1) = true := by
  by_cases atFirst : i = first.1
  · subst i
    exact False.elim (no_return_at_restart first.2 ⟨_, edge.atStart.symm.trans returned⟩)
  by_cases atLast : i + 1 = last.1
  · have next := steps i
    rw [atLast, edge.atNext, returned] at next
    exact feedback_only next
  · exact False.elim (edge.inside i (by omega) (by omega) ⟨_, returned⟩)

private theorem covered {indices : Nat → Nat} (start : indices 0 = 0)
    (later : ∀ n, indices n + 1 < indices (n + 1)) (i : Nat) :
    ∃ n, indices n ≤ i ∧ i < indices (n + 1) := by
  classical
  have grows : ∀ n, n ≤ indices n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := later n; omega
  have bounded : ∃ n, i < indices (n + 1) := ⟨i, by have := grows (i + 1); omega⟩
  refine ⟨Nat.find bounded, ?_, Nat.find_spec bounded⟩
  generalize equation : Nat.find bounded = k
  cases k with
  | zero => rw [start]; exact Nat.zero_le _
  | succ n =>
    have earlier : n < Nat.find bounded := by rw [equation]; omega
    exact Nat.le_of_not_gt (Nat.find_min bounded earlier)

theorem stays_of_decomposes (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (split : Decomposes body parent input micro) :
    StaysInLoop body parent micro := by
  intro i tag values returned
  rcases split with ⟨inputs, indices, _, trace⟩ | ⟨last, path, forever⟩
  · obtain ⟨n, lower, upper⟩ := covered trace.first trace.later i
    have edge : Interval body parent micro (indices n, inputs n) (indices (n + 1), inputs (n + 1)) :=
      ⟨trace.atRestart n, trace.atRestart (n + 1), trace.later n, trace.bodyReturn n, trace.inside n⟩
    exact interval_stays steps edge i lower upper tag values returned
  · by_cases earlier : i < last.1
    · clear forever
      induction path with
      | refl => exact False.elim (Nat.not_lt_zero _ earlier)
      | @tail previous last _ edge ih =>
        by_cases before : i < previous.1
        · exact ih before
        · exact interval_stays steps edge i (by omega) earlier tag values returned
    · by_cases atLast : i = last.1
      · subst i
        exact False.elim (no_return_at_restart last.2 ⟨_, forever.1.symm.trans returned⟩)
      · exact False.elim (forever.2 i (by omega) ⟨_, returned⟩)

theorem body_decomposes (steps : ∀ i, Step (micro i) (micro (i + 1)))
    (initial : micro 0 = .eval (.region body input (PUnit.unit : Locals m.Val [])) (.loop body parent))
    (stays : StaysInLoop body parent micro) :
    Decomposes body parent input (withEntry body parent input micro) := by
  apply decompose ?_ rfl ?_
  · intro i
    cases i with
    | zero =>
      change Step (restart body parent input) (micro 0)
      rw [initial]
      rfl
    | succ i => exact steps i
  · intro i tag values returned
    cases i with
    | zero => exact False.elim (no_return_at_restart input ⟨_, returned⟩)
    | succ i => exact stays i tag values returned

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Proofs
