module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Route
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.FollowGraph

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops)

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}
  {O : Ops Φ α σ} {env : Env α} {route : Route α σ} {n : Nat}

namespace Route

theorem under_in {i : Nat} {a : Value α} {s : σ} {j : Nat} {b : Value α}
    (h : i < n) : Route.under n route i a s j b ↔ j = i ∧ b = a := by simp [Route.under, h]

theorem under_out {i : Nat} {a : Value α} {s : σ} {j : Nat} {b : Value α}
    (h : n ≤ i) : Route.under n route i a s j b ↔ ∃ k, j = n + k ∧ route (i - n) a s k b := by
  simp [Route.under, Nat.not_lt.mpr h]

end Route

namespace Routed

variable {r t : Region Φ}

private theorem eval_internal (h : Routed O env r t (Route.under n route))
    {s t' : σ} {j : Nat} {v : Value α} (inside : j < n) :
    Semantics.Region.Eval O.instr env t s j v t' ↔ Semantics.Region.Eval O.instr env r s j v t' := by
  rw [h.eval]
  constructor
  · rintro ⟨i, a, run, step⟩
    by_cases hi : i < n
    · obtain ⟨rfl, rfl⟩ := (Route.under_in hi).mp step
      exact run
    · obtain ⟨k, rfl, _⟩ := (Route.under_out (Nat.le_of_not_lt hi)).mp step
      omega
  · exact fun run => ⟨j, v, run, (Route.under_in inside).mpr ⟨rfl, rfl⟩⟩

private theorem eval_external (h : Routed O env r t (Route.under n route))
    {s t' : σ} {j : Nat} {v : Value α} :
    Semantics.Region.Eval O.instr env t s (n + j) v t' ↔
      ∃ k a, Semantics.Region.Eval O.instr env r s (n + k) a t' ∧ route k a t' j v := by
  rw [h.eval]
  constructor
  · rintro ⟨i, a, run, step⟩
    by_cases hi : i < n
    · obtain ⟨eq, _⟩ := (Route.under_in hi).mp step
      omega
    · obtain ⟨k, eq, route⟩ := (Route.under_out (Nat.le_of_not_lt hi)).mp step
      have hk : k = j := by omega
      have entry : n + (i - n) = i := by omega
      exact ⟨i - n, a, by simpa only [entry] using run, hk ▸ route⟩
  · rintro ⟨k, a, run, step⟩
    exact ⟨n + k, a, run, (Route.under_out (Nat.le_add_right n k)).mpr
      ⟨j, rfl, by simpa only [Nat.add_sub_cancel_left] using step⟩⟩

variable {bs cs : Fin n → Region Φ}
variable (blocks : ∀ i v, Routed O (extend env v) (bs i) (cs i) (Route.under n route))

local notation "source" => followGraph O.instr O.faults O.prim env bs
local notation "target" => followGraph O.instr O.faults O.prim env cs

include blocks in
private theorem same_steps : (target).step = (source).step := by
  funext p q
  apply propext
  constructor
  · rintro ⟨hi, hj, run⟩
    exact ⟨hi, hj, ((blocks ⟨_, hi⟩ p.payload).eval_internal hj).mp run⟩
  · rintro ⟨hi, hj, run⟩
    exact ⟨hi, hj, ((blocks ⟨_, hi⟩ p.payload).eval_internal hj).mpr run⟩

private theorem stays_inside {p q : Jump α σ} (hi : p.label < n) (path : (source).Reaches p q) :
    q.label < n := by
  cases path with
  | refl => exact hi
  | tail _ edge => exact edge.choose_spec.1

include blocks

private theorem same_fault {p : Jump α σ} {t : σ} :
    Semantics.Region.FollowFault O.instr O.faults env cs p.label p.payload p.state t ↔
      Semantics.Region.FollowFault O.instr O.faults env bs p.label p.payload p.state t := by
  rw [← follow_fault (prim := O.prim), ← follow_fault (prim := O.prim)]
  have finish (q : Jump α σ) : (target).finish q (.fault t) ↔ (source).finish q (.fault t) :=
    ⟨fun ⟨hi, run⟩ => ⟨hi, (blocks ⟨_, hi⟩ q.payload).fault.mp run⟩,
      fun ⟨hi, run⟩ => ⟨hi, (blocks ⟨_, hi⟩ q.payload).fault.mpr run⟩⟩
  simp only [Graph.Finite, Graph.Reaches, same_steps blocks, finish]

private theorem same_div {p : Jump α σ} :
    External.Diverges O.instr O.prim (.follow env cs p.label p.payload p.state) ↔
      External.Diverges O.instr O.prim (.follow env bs p.label p.payload p.state) := by
  rw [← follow_div (faults := O.faults), ← follow_div (faults := O.faults)]
  have finish (q : Jump α σ) : (target).finish q .diverge ↔ (source).finish q .diverge :=
    ⟨fun ⟨hi, run⟩ => ⟨hi, (blocks ⟨_, hi⟩ q.payload).div.mp run⟩,
      fun ⟨hi, run⟩ => ⟨hi, (blocks ⟨_, hi⟩ q.payload).div.mpr run⟩⟩
  simp only [Graph.Finite, Graph.Reaches, Graph.Infinite, same_steps blocks, finish]

private theorem routed_return {p : Jump α σ} (hi : p.label < n) {j : Nat} {b : Value α} {t : σ} :
    Semantics.Region.Follow O.instr env cs p.label p.payload p.state j b t ↔
      ∃ k a, Semantics.Region.Follow O.instr env bs p.label p.payload p.state k a t ∧ route k a t j b := by
  rw [← follow_ret (faults := O.faults) (prim := O.prim)]
  simp only [← follow_ret (faults := O.faults) (prim := O.prim), Graph.Finite, Graph.Reaches, same_steps blocks]
  constructor
  · rintro ⟨q, reach, finish⟩
    rcases finish with ⟨out, _⟩ | ⟨here, run⟩
    · exact (Nat.not_le_of_lt (stays_inside hi reach) out).elim
    · obtain ⟨k, a, run, mapped⟩ := ((blocks ⟨_, here⟩ q.payload).eval_external).mp run
      exact ⟨k, a, ⟨q, reach, .inr ⟨here, run⟩⟩, mapped⟩
  · rintro ⟨k, a, ⟨q, reach, finish⟩, mapped⟩
    rcases finish with ⟨out, _⟩ | ⟨here, run⟩
    · exact (Nat.not_le_of_lt (stays_inside hi reach) out).elim
    · exact ⟨q, reach, .inr ⟨here, ((blocks ⟨_, here⟩ q.payload).eval_external).mpr ⟨k, a, run, mapped⟩⟩⟩

theorem cfg {e f : Region Φ} (entry : Routed O env e f (Route.under n route)) :
    Routed O env (.cfg e n bs) (.cfg f n cs) route where
  eval := by
    intro s j b t
    constructor
    · intro run
      cases run with
      | @cfg _ _ _ _ _ mid _ initial _ first _ head tail =>
        obtain ⟨i, a, start, mapped⟩ := entry.eval.mp head
        by_cases hi : i < n
        · obtain ⟨rfl, rfl⟩ := (Route.under_in hi).mp mapped
          obtain ⟨out, v, tail, route⟩ := (routed_return blocks (p := ⟨_, _, mid⟩) hi).mp tail
          exact ⟨out, v, .cfg start tail, route⟩
        · have outside := Nat.le_of_not_lt hi
          obtain ⟨k, rfl, routedOut⟩ := (Route.under_out outside).mp mapped
          cases tail with
          | exit _ => exact ⟨i - n, a, .cfg start (.exit outside), by
              simpa only [Nat.add_sub_cancel_left] using routedOut⟩
          | step internal _ _ => omega
    · rintro ⟨out, v, run, mapped⟩
      cases run with
      | @cfg _ _ _ _ _ mid _ initial _ first _ head tail =>
        by_cases hi : first < n
        · exact .cfg (entry.eval.mpr ⟨first, initial, head, (Route.under_in hi).mpr ⟨rfl, rfl⟩⟩)
            ((routed_return blocks (p := ⟨first, initial, mid⟩) hi).mpr ⟨out, v, tail, mapped⟩)
        · cases tail with
          | exit outside =>
            refine .cfg (entry.eval.mpr ⟨_, _, head,
              (Route.under_out outside).mpr ⟨j, rfl, mapped⟩⟩) ?_
            simpa only [Nat.add_sub_cancel_left] using
              (Semantics.Region.Follow.exit (instr := O.instr) (env := env) (blocks := cs)
                (value := b) (s := t) (Nat.le_add_right n j))
          | step inside _ _ => exact (hi inside).elim
  fault := by
    intro s t
    constructor
    · intro run
      cases run with
      | cfg_entry run => exact .cfg_entry (entry.fault.mp run)
      | @cfg_follow _ _ _ _ _ mid _ i a head tail =>
        have hi : i < n := by cases tail <;> assumption
        exact .cfg_follow (entry.eval_internal hi |>.mp head)
          ((same_fault blocks (p := ⟨i, a, mid⟩)).mp tail)
    · intro run
      cases run with
      | cfg_entry run => exact .cfg_entry (entry.fault.mpr run)
      | @cfg_follow _ _ _ _ _ mid _ i a head tail =>
        have hi : i < n := by cases tail <;> assumption
        exact .cfg_follow (entry.eval_internal hi |>.mpr head)
          ((same_fault blocks (p := ⟨i, a, mid⟩)).mpr tail)
  div := by
    intro s
    constructor
    · intro run
      cases run.unfold with
      | core step => cases step with
        | cfg_entry run => exact .fold_core (.cfg_entry (entry.div.mp run))
        | @cfg_follow _ _ _ _ _ mid i a head tail =>
          have hi : i < n := by cases tail.unfold with | core step => cases step <;> assumption
          exact .fold_core (.cfg_follow (entry.eval_internal hi |>.mp head)
            ((same_div blocks (p := ⟨i, a, mid⟩)).mp tail))
    · intro run
      cases run.unfold with
      | core step => cases step with
        | cfg_entry run => exact .fold_core (.cfg_entry (entry.div.mpr run))
        | @cfg_follow _ _ _ _ _ mid i a head tail =>
          have hi : i < n := by cases tail.unfold with | core step => cases step <;> assumption
          exact .fold_core (.cfg_follow (entry.eval_internal hi |>.mpr head)
            ((same_div blocks (p := ⟨i, a, mid⟩)).mpr tail))

end Routed

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity
