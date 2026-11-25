module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Segments

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Proofs

open Recursive.Tail (Activation)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {outs : Ports (Ty V S)}
variable {base stack : Stack m outs outs}

theorem stream_segments (run : Nat → Activation m outs)
    (edges : ∀ n, Tail.Prefix.Step m (run n) (run (n + 1))) (frames : ForwardedOver base stack) :
    ∃ framesAt : Nat → Stack m outs outs, framesAt 0 = stack ∧
      (∀ n, ForwardedOver base (framesAt n)) ∧
      ∀ n, CallSegment (callState (run n) (framesAt n)) (callState (run (n + 1)) (framesAt (n + 1))) := by
  classical
  let extend (n : Nat) (current : {k // ForwardedOver base k}) :
      {k // ForwardedOver base k ∧ CallSegment (callState (run n) current.val) (callState (run (n + 1)) k)} :=
    Classical.indefiniteDescription _ (step_segment (edges n) current.property)
  let framesAt : Nat → {k // ForwardedOver base k} :=
    Nat.rec ⟨stack, frames⟩ fun n current => ⟨(extend n current).val, (extend n current).property.1⟩
  exact ⟨fun n => (framesAt n).val, rfl, fun n => (framesAt n).property, fun n => (extend n (framesAt n)).property.2⟩

private theorem segments_infinite (boundary : Nat → State m outs)
    (segments : ∀ n, CallSegment (boundary n) (boundary (n + 1))) :
    InfiniteTrace Step (boundary 0) := by
  apply InfiniteTrace.coinduct (fun current => ∃ n, TransGen Step current (boundary n)) ?_
    ⟨1, segment_steps (segments 0)⟩
  rintro current ⟨n, path⟩
  obtain ⟨next, edge, rest⟩ := TransGen.head'_iff.mp path
  refine ⟨next, edge, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp rest with equal | later
  · subst next
    exact ⟨n + 1, segment_steps (segments n)⟩
  · exact ⟨n, later⟩

private theorem noncall_indices (micro : Nat → State m outs)
    (edges : ∀ n, Step (micro n) (micro (n + 1))) {index : Nat} {target : State m outs}
    (path : NoncallPath (micro index) target) :
    ∃ count, micro (index + count) = target ∧
      ∀ j, 0 < j → j ≤ count → ¬ IsCall (micro (index + j)) := by
  induction path with
  | refl => exact ⟨0, rfl, fun j positive bounded => False.elim (Nat.not_lt_of_ge bounded positive)⟩
  | @tail _ lastState _ edge ih =>
    obtain ⟨count, hits, between⟩ := ih
    have reached : micro (index + (count + 1)) = lastState := by
      rw [Nat.add_succ]
      exact step_deterministic (edges (index + count)) (hits.symm ▸ edge.1)
    refine ⟨count + 1, reached, fun j positive bounded => ?_⟩
    by_cases earlier : j ≤ count
    · exact between j positive earlier
    · have last : j = count + 1 := by omega
      rw [last, reached]
      exact edge.2

private theorem segment_indices (micro : Nat → State m outs)
    (edges : ∀ n, Step (micro n) (micro (n + 1))) {index : Nat} {target : State m outs}
    (seg : CallSegment (micro index) target) :
    ∃ count, 0 < count ∧ micro (index + count) = target ∧
      ∀ j, 0 < j → j < count → ¬ IsCall (micro (index + j)) := by
  obtain ⟨_, path, edge, _⟩ := seg
  obtain ⟨count, reached, between⟩ := noncall_indices micro edges path
  refine ⟨count + 1, Nat.zero_lt_succ _, ?_, fun j after before => between j after (Nat.le_of_lt_succ before)⟩
  rw [Nat.add_succ]
  exact step_deterministic (edges (index + count)) (reached.symm ▸ edge)

theorem segments_microsteps (boundary : Nat → State m outs)
    (segments : ∀ n, CallSegment (boundary n) (boundary (n + 1))) :
    ∃ (micro : Nat → State m outs) (indices : Nat → Nat),
      indices 0 = 0 ∧
      (∀ n, Step (micro n) (micro (n + 1))) ∧
      (∀ n, indices n < indices (n + 1)) ∧
      (∀ n, micro (indices n) = boundary n) ∧
      ∀ n j, indices n < j → j < indices (n + 1) → ¬ IsCall (micro j) := by
  classical
  obtain ⟨micro, initial, edges⟩ := segments_infinite boundary segments
  let jump (n : Nat) (i : {i // micro i = boundary n}) :
      {count // 0 < count ∧ micro (i.val + count) = boundary (n + 1) ∧
        ∀ j, 0 < j → j < count → ¬ IsCall (micro (i.val + j))} :=
    Classical.indefiniteDescription _ (segment_indices micro edges (i.property.symm ▸ segments n))
  let index : (n : Nat) → {i // micro i = boundary n} :=
    Nat.rec ⟨0, initial⟩ fun n i => ⟨i.val + (jump n i).val, (jump n i).property.2.1⟩
  refine ⟨micro, fun n => (index n).val, rfl, edges, fun n => ?_, fun n => (index n).property, ?_⟩
  · exact Nat.lt_add_of_pos_right (jump n (index n)).property.1
  · intro n j after before
    let start := (index n).val
    let count := (jump n (index n)).val
    change start < j at after
    change j < start + count at before
    have quiet := (jump n (index n)).property.2.2 (j - start) (by omega) (by omega)
    change ¬ IsCall (micro (start + (j - start))) at quiet
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt after)] using quiet

private theorem noncall_path_of_indices (micro : Nat → State m outs)
    (edges : ∀ n, Step (micro n) (micro (n + 1))) (start count : Nat)
    (inside : ∀ j, 0 < j → j ≤ count → ¬ IsCall (micro (start + j))) :
    NoncallPath (micro start) (micro (start + count)) := by
  induction count with
  | zero => exact .refl
  | succ count ih =>
    rw [Nat.add_succ]
    exact (ih fun j positive bounded => inside j positive (Nat.le_succ_of_le bounded)).tail
      ⟨edges _, by simpa only [Nat.add_succ] using inside (count + 1) (Nat.zero_lt_succ _) (Nat.le_refl _)⟩

theorem microsteps_segments (micro : Nat → State m outs) (indices : Nat → Nat)
    (edges : ∀ n, Step (micro n) (micro (n + 1))) (rising : ∀ n, indices n < indices (n + 1))
    (calls : ∀ n, IsCall (micro (indices n)))
    (inside : ∀ n j, indices n < j → j < indices (n + 1) → ¬ IsCall (micro j)) :
    ∀ n, CallSegment (micro (indices n)) (micro (indices (n + 1))) := by
  intro n
  let count := indices (n + 1) - indices n - 1
  have interval : indices n + count + 1 = indices (n + 1) := by
    have grows := rising n
    dsimp [count]
    omega
  have quiet := noncall_path_of_indices micro edges (indices n) count (fun j positive bounded =>
    inside n (indices n + j) (by omega) (by omega))
  exact ⟨_, quiet, interval ▸ edges (indices n + count), calls (n + 1)⟩

theorem diverges_microsteps {activation : Activation m outs}
    (productive : Tail.Prefix.Diverges m activation) :
    InfiniteTrace Step (callState activation .halt) := by
  obtain ⟨run, first, edges⟩ := productive
  obtain ⟨framesAt, empty, _, segments⟩ := stream_segments run edges (.base (base := .halt))
  simpa only [first, empty] using segments_infinite (fun n => callState (run n) (framesAt n)) segments

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Proofs
