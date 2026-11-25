module

public import Silmaril.Languages.Python.Core.Defs
public import Silmaril.Semantics.Operational.Determinism.Fuel.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core

open Silmaril.Languages.Python.Core Silmaril.Semantics.Operational

variable {profile : Profile} {expr : Expr} {next : Except Exception Expr}
  {source target : State} {label : Option Completion}

theorem bin_eval_iff {op : BinOp} {left right : Int} {result : Completion} :
    op.eval left right = result ↔ op.Eval left right result := by
  constructor
  · rintro rfl
    cases op with
    | add => exact .add ..
    | floorDiv =>
      by_cases zero : right = 0
      · subst right
        exact .divZero left
      · simpa [BinOp.eval, zero] using BinOp.Eval.div left right zero
  · intro h
    cases h <;> simp_all [BinOp.eval]

private theorem reduce_sound (h : expr.reduce = some next) : expr.Step next := by
  induction expr generalizing next with
  | int => simp [Expr.reduce] at h
  | binary op left right leftIH rightIH =>
    cases left with
    | int a =>
      cases right with
      | int b =>
        have eq := Option.some.inj h
        rw [← eq]
        exact .compute (bin_eval_iff.mp rfl)
      | binary rop rl rr =>
        obtain ⟨inner, reduced, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .right (rightIH reduced)
    | binary lop ll lr =>
      obtain ⟨inner, reduced, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .left (leftIH reduced)

private theorem reduce_complete (h : expr.Step next) : expr.reduce = some next := by
  induction h with
  | @left op left right next step ih =>
    cases left with
    | int => cases step
    | binary => rw [Expr.reduce, ih]; rfl
  | @right op left right next step ih =>
    cases right with
    | int => cases step
    | binary => rw [Expr.reduce, ih]; rfl
  | compute eval => simp [Expr.reduce, bin_eval_iff.mpr eval]

theorem reduce_iff : expr.reduce = some next ↔ expr.Step next :=
  ⟨reduce_sound, reduce_complete⟩

private theorem advance_sound (h : source.advance = some (label, target)) : Step source label target := by
  cases source with
  | returning expr =>
    cases expr with
    | int value =>
      cases h
      exact .ret value
    | binary op left right =>
      obtain ⟨inner, reduced, eq⟩ := Option.map_eq_some_iff.mp h
      cases eq
      exact .expr (reduce_iff.mp reduced)
  | raising error =>
    cases h
    exact .raise error
  | finished => simp [State.advance] at h

private theorem advance_complete (h : Step source label target) : source.advance = some (label, target) := by
  cases h with
  | @expr expr next step =>
    cases expr with
    | int => cases step
    | binary => simp [State.advance, reduce_iff.mpr step]
  | ret => rfl
  | raise => rfl

theorem advance_iff : source.advance = some (label, target) ↔ Step source label target :=
  ⟨advance_sound, advance_complete⟩

theorem step_deterministic {other : State} {otherLabel : Option Completion}
    (left : Step source label target) (right : Step source otherLabel other) :
    label = otherLabel ∧ target = other := by
  have eq := (advance_iff.mpr left).symm.trans (advance_iff.mpr right)
  exact Prod.mk.inj (Option.some.inj eq)

theorem detFrom (profile : Profile) (start : State) : (semantics profile).toOpSem.DetFrom start := by
  intro source _
  constructor
  · rintro left right ⟨_, _, l⟩ ⟨_, _, r⟩
    exact (step_deterministic l r).2
  · rintro left right ⟨_, l⟩ ⟨_, r⟩
    cases l
    cases r
    rfl

theorem terminal (profile : Profile) : (semantics profile).toOpSem.TerminalDiscipline := by
  rintro source outcome ⟨_, observed⟩ target ⟨_, _, step⟩
  cases observed
  cases step

private theorem expr_progress (expr : Expr) :
    (∃ value, expr = .int value) ∨ ∃ next, expr.Step next := by
  induction expr with
  | int value => exact Or.inl ⟨value, rfl⟩
  | binary op left right leftIH rightIH =>
    apply Or.inr
    rcases leftIH with ⟨a, rfl⟩ | ⟨next, step⟩
    · rcases rightIH with ⟨b, rfl⟩ | ⟨next, step⟩
      · exact ⟨_, .compute (bin_eval_iff.mp rfl)⟩
      · exact ⟨_, .right step⟩
    · exact ⟨_, .left step⟩

theorem progress (supported : source.supported profile) :
    (∃ label target, (labelled profile).step source label target) ∨
      (semantics profile).observe source (.returned source.result) := by
  cases source with
  | returning expr =>
    rcases expr_progress expr with ⟨value, rfl⟩ | ⟨next, step⟩
    · exact Or.inl ⟨_, _, supported, .ret value⟩
    · exact Or.inl ⟨_, _, supported, .expr step⟩
  | raising error => exact Or.inl ⟨_, _, supported, .raise error⟩
  | finished result => exact Or.inr ⟨supported, .finished result⟩

private theorem pick_running_valid {selected : Option (Option Completion × State)}
    (advance : source.advance = selected)
    (unobserved : ∀ outcome, ¬ Observes source outcome) :
    (selected.elim (.stop .stuck) fun transition => Decision.move transition.2).Valid
      (WithUB.ofOpSem ordinary) source := by
  cases selected with
  | none =>
    refine ⟨?_, unobserved⟩
    rintro target ⟨label, step⟩
    have impossible := advance.symm.trans (advance_iff.mpr step)
    cases impossible
  | some transition =>
    obtain ⟨label, target⟩ := transition
    exact ⟨label, advance_iff.mp advance⟩

theorem pick_valid (source : State) :
    source.pick.Valid (WithUB.ofOpSem ordinary) source := by
  cases source with
  | returning expr =>
    exact pick_running_valid (source := .returning expr) rfl (fun _ h => by cases h)
  | raising error =>
    exact pick_running_valid (source := .raising error) rfl (fun _ h => by cases h)
  | finished result => exact .finished result

theorem pick_known (profile : Profile) (source : State) :
    (if source.supported profile then source.pick else .stop .ub) ≠ .stop .unknown := by
  by_cases supported : source.supported profile
  · simp only [supported, ite_true]
    cases source with
    | returning expr =>
      simp only [State.pick]
      cases (State.returning expr).advance <;> simp [Option.elim]
    | raising error => simp [State.pick, State.advance]
    | finished result => simp [State.pick]
  · simp [supported]

end Silmaril.Proofs.Languages.Python.Core
