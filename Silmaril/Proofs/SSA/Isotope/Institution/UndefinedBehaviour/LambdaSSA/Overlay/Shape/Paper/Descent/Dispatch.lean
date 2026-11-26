module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Sequence

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops)

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}

@[expose] def Exit.shift (n : Nat) : Exit α σ → Exit α σ
  | .ret j a t => .ret (n + j) a t
  | .fault t => .fault t
  | .diverge => .diverge

/-- The prefix is protected. Only a return to an outer label enters the
postcontinuation. Its successful exits are shifted past the prefix. -/
@[expose] def Post.under (k : Post α σ) (n : Nat) : Post α σ :=
  fun p o => if p.label < n then o = .ret p.label p.payload p.state
    else ∃ e, o = Exit.shift n e ∧ k ⟨p.label - n, p.payload, p.state⟩ e

private theorem shift_injective (n : Nat) : Function.Injective (@Exit.shift α σ n) := by
  intro e d eq
  cases e <;> cases d <;> simp_all [Exit.shift]

private theorem ret_unshifted {n i : Nat} (hi : i < n) {v : Value α} {t : σ} (e : Exit α σ) :
    Exit.shift n e ≠ .ret i v t := by
  intro eq
  cases e with
  | ret j _ _ =>
    have h := (Exit.ret.inj eq).1
    omega
  | fault | diverge => cases eq

private theorem under_local {k : Post α σ} {n i : Nat} {v : Value α} {t : σ} (hi : i < n)
    (e : Exit α σ) : (k.under n).apply e (.ret i v t) ↔ e = .ret i v t := by
  cases e with
  | ret j a s =>
    by_cases hj : j < n
    · simp only [Post.apply, Post.under, ite_eq_left hj, eq_comm]
    · simp only [Post.apply, Post.under, ite_eq_right hj]
      exact ⟨fun ⟨x, eq, _⟩ => (ret_unshifted hi x eq.symm).elim,
        fun eq => (hj ((Exit.ret.inj eq).1.symm ▸ hi)).elim⟩
  | fault | diverge => simp [Post.apply]

private theorem under_shift {k : Post α σ} {n : Nat} (e o : Exit α σ) :
    (k.under n).apply (Exit.shift n e) (Exit.shift n o) ↔ k.apply e o := by
  cases e with
  | ret j a t =>
    simp only [Exit.shift, Post.apply, Post.under, ite_eq_right (Nat.not_lt.mpr (Nat.le_add_right n j)),
      Nat.add_sub_cancel_left]
    exact ⟨fun ⟨d, eq, h⟩ => shift_injective n eq ▸ h,
      fun h => ⟨o, rfl, h⟩⟩
  | fault | diverge =>
    exact ⟨fun h => shift_injective n h, fun h => congrArg (Exit.shift n) h⟩

private theorem under_shifted {k : Post α σ} {n : Nat} {o : Exit α σ} {P : Exit α σ → Prop} :
    (∃ e, P e ∧ (k.under n).apply e (Exit.shift n o)) ↔
      ∃ e, P (Exit.shift n e) ∧ k.apply e o := by
  constructor
  · rintro ⟨e, run, h⟩
    have lift : ∃ d, Exit.shift n d = e := by
      cases e with
      | fault t => exact ⟨.fault t, rfl⟩
      | diverge => exact ⟨.diverge, rfl⟩
      | ret i a t =>
        by_cases hi : i < n
        · exact (ret_unshifted hi o (by simpa [Post.apply, Post.under, hi] using h)).elim
        · exact ⟨.ret (i - n) a t, by simp [Exit.shift, Nat.add_sub_of_le (Nat.le_of_not_lt hi)]⟩
    obtain ⟨d, rfl⟩ := lift
    exact ⟨d, run, (under_shift d o).mp h⟩
  · rintro ⟨e, run, h⟩
    exact ⟨_, run, (under_shift e o).mpr h⟩

variable {O : Ops Φ α σ} {env : Env α} {n : Nat} {bs cs : Fin n → Region Φ} {k : Post α σ}

abbrev resume (O : Ops Φ α σ) (env : Env α) (bs : Fin n → Region Φ) : Post α σ :=
  fun p o => o ∈ (followGraph O.instr O.faults O.prim env bs).outcomes p

theorem cfg_runs (e : Region Φ) (s : σ) (o : Exit α σ) :
    Runs O env (.cfg e n bs) s o ↔ ∃ d, Runs O env e s d ∧ (resume O env bs).apply d o := by
  have start {j a t} : resume O env bs ⟨j, a, t⟩ o ↔ _ := follow_outcomes ⟨j, a, t⟩ o
  constructor
  · intro run
    cases o with
    | ret => cases run with | cfg head tail => exact ⟨.ret _ _ _, head, start.mpr tail⟩
    | fault =>
      cases run with
      | cfg_entry head => exact ⟨.fault _, head, rfl⟩
      | cfg_follow head tail => exact ⟨.ret _ _ _, head, start.mpr tail⟩
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | core h => cases h with
        | cfg_entry head => exact ⟨.diverge, head, rfl⟩
        | cfg_follow head tail => exact ⟨.ret _ _ _, head, start.mpr tail⟩
  · rintro ⟨d, head, tail⟩
    cases d with
    | ret j a t =>
      have tail' := (start (j := j) (a := a) (t := t)).mp tail
      cases o
      · exact Semantics.Region.Eval.cfg head tail'
      · exact Semantics.Region.Fault.cfg_follow head tail'
      · exact External.Diverges.fold_core (.cfg_follow head tail')
    | fault =>
      have : o = _ := tail
      subst o
      exact Semantics.Region.Fault.cfg_entry head
    | diverge =>
      have : o = .diverge := tail
      subst o
      exact External.Diverges.fold_core (.cfg_entry head)

local notation "source" => followGraph O.instr O.faults O.prim env bs
local notation "target" => followGraph O.instr O.faults O.prim env cs

private theorem finish_inside {p : Jump α σ} (hi : p.label < n) (o : Exit α σ) :
    (source).finish p o ↔ Runs O (extend env p.payload) (bs ⟨p.label, hi⟩) p.state (Exit.shift n o) := by
  cases o <;> simp [followGraph, Nat.not_le_of_lt hi, hi, Runs, Exit.shift]

private theorem step_inside {p q : Jump α σ} (hi : p.label < n) (hj : q.label < n) :
    (source).step p q ↔
      Runs O (extend env p.payload) (bs ⟨p.label, hi⟩) p.state (.ret q.label q.payload q.state) := by
  simp [followGraph, hi, hj, Runs]

variable (blocks : ∀ i v, Sequenced O (extend env v) (bs i) (cs i) (k.under n))

include blocks in
private theorem same_steps : (target).step = (source).step := by
  funext p q
  apply propext
  by_cases hi : p.label < n
  · by_cases hj : q.label < n
    · rw [step_inside hi hj, step_inside hi hj, blocks ⟨p.label, hi⟩ p.payload p.state]
      simp only [under_local hj, exists_eq_right]
    · simp [followGraph, hj]
  · simp [followGraph, hi]

private theorem reach_inside {p q : Jump α σ} (hi : p.label < n) (h : (source).Reaches p q) :
    q.label < n := by
  cases h with
  | refl => exact hi
  | tail _ step => exact step.choose_spec.1

include blocks in
private theorem resume_inside {p : Jump α σ} (hi : p.label < n) (o : Exit α σ) :
    resume O env cs p o ↔ ∃ e, resume O env bs p e ∧ k.apply e o := by
  have finite : (target).Finite p o ↔ ∃ e, (source).Finite p e ∧ k.apply e o := by
    simp only [Graph.Finite, Graph.Reaches, same_steps blocks]
    constructor
    · rintro ⟨q, path, finish⟩
      have hq := reach_inside hi path
      have run := (finish_inside hq o).mp finish
      obtain ⟨e, run, post⟩ := under_shifted.mp ((blocks ⟨q.label, hq⟩ q.payload _ _).mp run)
      exact ⟨e, ⟨q, path, (finish_inside hq e).mpr run⟩, post⟩
    · rintro ⟨e, ⟨q, path, finish⟩, post⟩
      have hq := reach_inside hi path
      refine ⟨q, path, (finish_inside hq o).mpr ?_⟩
      exact (blocks ⟨q.label, hq⟩ q.payload _ _).mpr
        (under_shifted.mpr ⟨e, (finish_inside hq e).mp finish, post⟩)
  change (_ ∨ o = .diverge ∧ (target).Infinite p) ↔
    ∃ e, (_ ∨ e = .diverge ∧ (source).Infinite p) ∧ k.apply e o
  have infinite : (target).Infinite p ↔ (source).Infinite p := by rw [Graph.Infinite, Graph.Infinite, same_steps blocks]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · obtain ⟨e, run, post⟩ := finite.mp h
      exact ⟨e, .inl run, post⟩
    · exact ⟨.diverge, .inr ⟨rfl, infinite.mp h⟩, rfl⟩
  · rintro ⟨e, (h | ⟨rfl, h⟩), post⟩
    · exact .inl (finite.mpr ⟨e, h, post⟩)
    · exact .inr ⟨post, infinite.mpr h⟩

private theorem resume_outside {p : Jump α σ} (hi : n ≤ p.label) (o : Exit α σ) :
    resume O env bs p o ↔ o = .ret (p.label - n) p.payload p.state := by
  rw [show resume O env bs p o ↔ _ from follow_outcomes p o]
  cases o with
  | ret =>
    constructor
    · intro h
      cases h with
      | exit _ => rfl
      | step inside _ _ => omega
    · intro h
      cases h
      exact .exit hi
  | fault =>
    constructor
    · intro h
      cases h <;> omega
    · intro h
      cases h
  | diverge =>
    constructor
    · intro h
      cases h.unfold with | core h => cases h <;> omega
    · intro h
      cases h

include blocks in
private theorem resume_commutes (e o : Exit α σ) :
    (∃ d, (k.under n).apply e d ∧ (resume O env cs).apply d o) ↔
      ∃ d, (resume O env bs).apply e d ∧ k.apply d o := by
  cases e with
  | fault | diverge => simp [Post.apply]
  | ret i a t =>
    by_cases hi : i < n
    · simpa only [Post.apply, Post.under, ite_eq_left hi, exists_eq_left] using resume_inside blocks (p := ⟨i, a, t⟩) hi o
    · change (∃ d, (if i < n then _ else _) ∧ (resume O env cs).apply d o) ↔
          ∃ d, resume O env bs ⟨i, a, t⟩ d ∧ k.apply d o
      simp only [resume_outside (p := ⟨i, a, t⟩) (Nat.le_of_not_lt hi)]
      simp only [ite_eq_right hi, exists_eq_left]
      constructor
      · rintro ⟨d, ⟨e, rfl, h⟩, tail⟩
        have eq : o = e := by
          cases e with
          | fault | diverge => exact tail
          | ret j v s =>
            simpa only [Exit.shift, Nat.add_sub_cancel_left] using
              (resume_outside (p := ⟨n + j, v, s⟩) (Nat.le_add_right n j) o).mp tail
        exact eq.symm ▸ h
      · intro h
        refine ⟨Exit.shift n o, ⟨o, rfl, h⟩, ?_⟩
        cases o with
        | fault | diverge => rfl
        | ret j v s =>
          exact (resume_outside (p := ⟨n + j, v, s⟩) (Nat.le_add_right n j) _).mpr
            (by simp only [Nat.add_sub_cancel_left])

theorem Sequenced.cfg {e f : Region Φ}
    (head : Sequenced O env e f (k.under n)) (blocks : ∀ i v, Sequenced O (extend env v) (bs i) (cs i) (k.under n)) :
    Sequenced O env (.cfg e n bs) (.cfg f n cs) k := by
  intro s o
  constructor
  · intro run
    obtain ⟨d, head', tail⟩ := (cfg_runs _ _ _).mp run
    obtain ⟨a, entry, routed⟩ := (head s d).mp head'
    obtain ⟨b, tail', post⟩ := (resume_commutes blocks a o).mp ⟨d, routed, tail⟩
    exact ⟨b, (cfg_runs _ _ _).mpr ⟨a, entry, tail'⟩, post⟩
  · rintro ⟨b, run, post⟩
    obtain ⟨a, entry, tail⟩ := (cfg_runs _ _ _).mp run
    obtain ⟨d, routed, tail'⟩ := (resume_commutes blocks a o).mpr ⟨b, tail, post⟩
    exact (cfg_runs _ _ _).mpr ⟨d, (head s d).mpr ⟨a, entry, routed⟩, tail'⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
