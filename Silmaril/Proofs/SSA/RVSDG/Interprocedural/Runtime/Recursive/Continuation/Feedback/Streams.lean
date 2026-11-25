module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Delimiter

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Proofs

open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {carried ports final : Ports (Ty V S)}
variable {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {parent : Stack m carried final} {input next : Tuple m.Val carried}

theorem iteration_iff_segment : Iteration body input next ↔ Segment body parent input next := by
  constructor
  · rintro ⟨tag, returned, again⟩
    refine ⟨tag, (returns_iff_delimited (.loop body parent)).mp returned, ?_⟩
    change some (State.finishLoop body tag next parent) = some (restart body parent next)
    rw [State.finishLoop, ite_eq_left again]
    rfl
  · rintro ⟨tag, bodyPath, feedback⟩
    refine ⟨tag, (returns_iff_delimited (.loop body parent)).mpr bodyPath, ?_⟩
    by_contra stops
    change some (State.finishLoop body tag next parent) = some (restart body parent next) at feedback
    rw [State.finishLoop, ite_eq_right stops] at feedback
    cases feedback

private theorem enter_body (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (input : Tuple m.Val carried) :
    Step (restart body parent input) (.eval (.region body input PUnit.unit) (.loop body parent)) := rfl

theorem segment_steps (segment : Segment body parent input next) :
    TransGen Step (restart body parent input) (restart body parent next) := by
  obtain ⟨_, path, feedback⟩ := segment
  have plain := ReflTransGen.mono (r := InsideStep (.loop body parent)) (fun _ _ edge => edge.1) _ _ path
  exact (TransGen.tail' plain feedback).head (enter_body body parent input)

private theorem segments_infinite (inputs : Nat → Tuple m.Val carried)
    (segments : ∀ n, Segment body parent (inputs n) (inputs (n + 1))) :
    InfiniteTrace Step (restart body parent (inputs 0)) := by
  apply InfiniteTrace.coinduct (fun state => ∃ n, TransGen Step state (restart body parent (inputs n)))
    ?_ ⟨1, segment_steps (segments 0)⟩
  rintro state ⟨n, path⟩
  obtain ⟨next, edge, rest⟩ := TransGen.head'_iff.mp path
  refine ⟨next, edge, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp rest with same | later
  · subst next
    exact ⟨n + 1, segment_steps (segments n)⟩
  · exact ⟨n, later⟩

private theorem body_indices (micro : Nat → State m final)
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (frame : Stack m ports final)
    {index : Nat} {target : State m final}
    (path : ReflTransGen (InsideStep frame) (micro index) target) :
    ∃ count, micro (index + count) = target ∧ ∀ j, j < count → ¬ atReturn frame (micro (index + j)) := by
  induction path with
  | refl => exact ⟨0, rfl, fun _ before => False.elim (Nat.not_lt_zero _ before)⟩
  | @tail _ target _ edge ih =>
    obtain ⟨count, reached, beforeReturn⟩ := ih
    have next : micro (index + (count + 1)) = target := by
      rw [Nat.add_succ]
      exact step_deterministic (steps (index + count)) (reached.symm ▸ edge.1)
    refine ⟨count + 1, next, fun j earlier => ?_⟩
    by_cases before : j < count
    · exact beforeReturn j before
    · have last : j = count := by omega
      rw [last, reached]
      exact edge.2

private theorem segment_indices (micro : Nat → State m final)
    (steps : ∀ i, Step (micro i) (micro (i + 1))) {index : Nat}
    (start : micro index = restart body parent input) (segment : Segment body parent input next) :
    ∃ count, 1 < count ∧ micro (index + count) = restart body parent next ∧
      (∃ tag, micro (index + count - 1) = .returned (.cons tag next) (.loop body parent)) ∧
      ∀ j, 0 < j → j + 1 < count → ¬ atReturn (.loop body parent) (micro (index + j)) := by
  obtain ⟨tag, localPath, feedback⟩ := segment
  have entry := step_deterministic (steps index) (start.symm ▸ enter_body body parent input)
  obtain ⟨count, returned, beforeReturn⟩ := body_indices micro steps (.loop body parent) (entry.symm ▸ localPath)
  refine ⟨count + 2, by omega, ?_, ⟨tag, ?_⟩, fun j positive earlier => ?_⟩
  · have exit := step_deterministic (steps (index + 1 + count)) (returned.symm ▸ feedback)
    rwa [show index + (count + 2) = index + 1 + count + 1 by omega]
  · rwa [show index + (count + 2) - 1 = index + 1 + count by omega]
  · have quiet := beforeReturn (j - 1) (by omega)
    rwa [show index + 1 + (j - 1) = index + j by omega] at quiet

theorem restarts_of_segments (inputs : Nat → Tuple m.Val carried)
    (segments : ∀ n, Segment body parent (inputs n) (inputs (n + 1))) :
    ∃ micro indices, RestartTrace body parent inputs micro indices := by
  classical
  obtain ⟨micro, first, steps⟩ := segments_infinite inputs segments
  let jump (n : Nat) (i : {i // micro i = restart body parent (inputs n)}) :
      {count // 1 < count ∧ micro (i.val + count) = restart body parent (inputs (n + 1)) ∧
        (∃ tag, micro (i.val + count - 1) = .returned (.cons tag (inputs (n + 1))) (.loop body parent)) ∧
        ∀ j, 0 < j → j + 1 < count → ¬ atReturn (.loop body parent) (micro (i.val + j))} :=
    Classical.indefiniteDescription _ (segment_indices micro steps i.property (segments n))
  let index : (n : Nat) → {i // micro i = restart body parent (inputs n)} :=
    Nat.rec ⟨0, first⟩ fun n i => ⟨i.val + (jump n i).val, (jump n i).property.2.1⟩
  refine ⟨micro, fun n => (index n).val, rfl, steps, fun n => (index n).property, ?_,
    fun n => (jump n (index n)).property.2.2.1, ?_⟩
  · intro n
    have longer := (jump n (index n)).property.1
    change (index n).val + 1 < (index n).val + (jump n (index n)).val
    omega
  · intro n j after before
    let start := (index n).val
    let count := (jump n (index n)).val
    change start < j at after
    change j + 1 < start + count at before
    have inside := (jump n (index n)).property.2.2.2 (j - start) (by omega) (by omega)
    change ¬ atReturn (.loop body parent) (micro (start + (j - start))) at inside
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt after)] using inside

private theorem inside_path (micro : Nat → State m final)
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (frame : Stack m ports final) (first count : Nat)
    (inside : ∀ j, j < count → ¬ atReturn frame (micro (first + j))) :
    ReflTransGen (InsideStep frame) (micro first) (micro (first + count)) := by
  induction count with
  | zero => exact .refl
  | succ count ih =>
    rw [Nat.add_succ]
    exact (ih fun j before => inside j (Nat.lt_trans before (Nat.lt_succ_self _))).tail
      ⟨steps _, inside count (Nat.lt_succ_self _)⟩

theorem segments_of_restarts {inputs : Nat → Tuple m.Val carried} {micro : Nat → State m final}
    {indices : Nat → Nat} (trace : RestartTrace body parent inputs micro indices) :
    ∀ n, Segment body parent (inputs n) (inputs (n + 1)) := by
  intro n
  let first := indices n + 1
  let exit := indices (n + 1) - 1
  have enough : first ≤ exit := by have := trace.later n; dsimp [first, exit]; omega
  have exitEdge : exit + 1 = indices (n + 1) := by have := trace.later n; dsimp [exit]; omega
  have entry := step_deterministic (trace.steps (indices n))
    ((trace.atRestart n).symm ▸ enter_body body parent (inputs n))
  obtain ⟨tag, returned⟩ := trace.bodyReturn n
  have path := inside_path micro trace.steps (.loop body parent) first (exit - first) (fun j before => by
    apply trace.inside n (first + j)
    · dsimp [first]; omega
    · omega)
  rw [Nat.add_sub_of_le enough] at path
  have feedback := trace.steps exit
  rw [exitEdge, trace.atRestart (n + 1)] at feedback
  exact ⟨tag, entry ▸ returned ▸ path, returned ▸ feedback⟩

theorem run_iff_restarts :
    Run body input ↔
      ∃ (inputs : Nat → Tuple m.Val carried) (micro : Nat → State m final) (indices : Nat → Nat),
        inputs 0 = input ∧ RestartTrace body parent inputs micro indices := by
  constructor
  · rintro ⟨inputs, first, steps⟩
    obtain ⟨micro, indices, trace⟩ :=
      restarts_of_segments (parent := parent) inputs (fun n => iteration_iff_segment.mp (steps n))
    exact ⟨inputs, micro, indices, first, trace⟩
  · rintro ⟨inputs, micro, indices, first, trace⟩
    exact ⟨inputs, first, fun n => iteration_iff_segment.mpr (segments_of_restarts trace n)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Proofs
