module

public import Silmaril.SSA.SeaOfNodes.GCM.Sink.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink

open Silmaril.SSA.SeaOfNodes.GCM.Sink
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env InstrDeterministic extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x

variable {Φ : Type u} {τ : Type v} {α : Type w} {σ : Type x}

section Typing

variable [TypeFormers τ] [HasTy Φ τ]

theorem before_hasType (op : Φ) :
    (before op).HasType (inputs (τ := τ) op) [instrTrg op] := by
  apply Region.HasType.cfg (fun _ => instrTrg op)
  · exact .let₁ (.op (.var rfl)) (.case (A := unit) (B := unit) (.var rfl)
      (.br rfl (.var rfl)) (.br rfl (.var rfl)))
  · intro _
    exact .br rfl (.var rfl)

theorem after_hasType (op : Φ) :
    (after op).HasType (inputs (τ := τ) op) [instrTrg op] := by
  apply Region.HasType.cfg (fun i => Fin.cases (instrSrc op) (fun _ => instrTrg op) i)
  · exact .case (A := unit) (B := unit) (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact .let₁ (.op (.var rfl)) (.br rfl (.var rfl))
    · exact .br rfl (.var rfl)

end Typing

theorem sink?_shape {r r' : Region Φ} :
    sink? r = some r' ↔ ∃ op, r = before op ∧ r' = after op := by
  constructor
  · intro changed
    unfold sink? at changed
    cases admitted : admit r with
    | none => simp [admitted] at changed
    | some form =>
      rw [admitted] at changed
      cases form with
      | entryLet op => exact ⟨op, rfl, (Option.some.inj changed).symm⟩
  · rintro ⟨op, rfl, rfl⟩
    rfl

private theorem deterministic (compute : Φ → Value α → Value α) :
    InstrDeterministic (instruction (σ := σ) compute) := by
  intro op arg start first finish second finish' h h'
  exact ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩

private def HasTag (v : Value α) : Prop :=
  (∃ payload, v = .inl payload) ∨ (∃ payload, v = .inr payload)

private theorem read_var {compute : Φ → Value α → Value α} {env : Env α} {i : Nat}
    {start finish : σ} {value : Value α}
    (run : Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval (instruction compute) env
      (.var i) start value finish) : env i = value := by
  cases run
  rfl

private theorem case_tag {compute : Φ → Value α → Value α} {env : Env α}
    {i label : Nat} {left right : Region Φ} {start finish : σ} {value : Value α}
    (run : Eval (instruction compute) env (.case (.var i) left right) start label value finish) :
    HasTag (env i) := by
  cases run with
  | case_inl discr _ => exact .inl ⟨_, read_var discr⟩
  | case_inr discr _ => exact .inr ⟨_, read_var discr⟩

private theorem before_tag {compute : Φ → Value α → Value α} {op : Φ}
    {env : Env α} {start finish : σ} {label : Nat} {value : Value α}
    (run : Eval (instruction compute) env (before op) start label value finish) :
    HasTag (env 0) := by
  cases run with
  | cfg entry _ =>
    cases entry with
    | let₁ _ dispatch =>
      have tagged := case_tag dispatch
      exact tagged

private theorem after_tag {compute : Φ → Value α → Value α} {op : Φ}
    {env : Env α} {start finish : σ} {label : Nat} {value : Value α}
    (run : Eval (instruction compute) env (after op) start label value finish) :
    HasTag (env 0) := by
  cases run with
  | cfg entry _ => exact case_tag entry

private theorem both_run (compute : Φ → Value α → Value α) (op : Φ)
    (env : Env α) (start : σ) {result : Value α} (selected : result? compute op env = some result) :
    Eval (instruction compute) env (before op) start 0 result start ∧
    Eval (instruction compute) env (after op) start 0 result start := by
  cases tag : env 0 with
  | inl payload =>
    have same : compute op (env 1) = result := by simpa [result?, tag] using selected
    subst result
    constructor
    · refine .cfg (.let₁ (.op .var ⟨rfl, rfl⟩) (.case_inl (.var_of_eq tag) (.br .var))) ?_
      exact .step (by decide) (.br .var) (.exit (by decide))
    · have localOp : Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval (instruction compute)
          (extend env (env 1)) (.op op (.var 0))
          start (compute op (env 1)) start := .op .var ⟨rfl, rfl⟩
      have runArm : Eval (instruction compute) (extend env (env 1))
          (.let₁ (.op op (.var 0)) forward) start 2 (compute op (env 1)) start :=
        .let₁ localOp (.br .var)
      refine .cfg (.case_inl (.var_of_eq tag) (.br .var)) ?_
      have inside : 0 < 2 := by decide
      refine .step (label := 0) (next := 2) inside ?_ (.exit (by decide))
      exact runArm
  | inr payload =>
    have same : env 2 = result := by simpa [result?, tag] using selected
    subst result
    constructor
    · refine .cfg (.let₁ (.op .var ⟨rfl, rfl⟩) (.case_inr (.var_of_eq tag) (.br .var))) ?_
      exact .step (by decide) (.br .var) (.exit (by decide))
    · refine .cfg (.case_inr (.var_of_eq tag) (.br .var)) ?_
      exact .step (by decide) (.br .var) (.exit (by decide))
  | atom _ | unit | pair _ _ => simp [result?, tag] at selected

private theorem observe (compute : Φ → Value α → Value α) (op : Φ) (r : Region Φ)
    (env : Env α) (start finish : σ) (label : Nat) (value : Value α)
    (tagged : Eval (instruction compute) env r start label value finish → HasTag (env 0))
    (runs : ∀ {result}, result? compute op env = some result →
      Eval (instruction compute) env r start 0 result start) :
    Eval (instruction compute) env r start label value finish ↔
      label = 0 ∧ result? compute op env = some value ∧ finish = start := by
  constructor
  · intro run
    have existsResult : ∃ observed, result? compute op env = some observed := by
      rcases tagged run with ⟨payload, tag⟩ | ⟨payload, tag⟩
      · exact ⟨compute op (env 1), by simp [result?, tag]⟩
      · exact ⟨env 2, by simp [result?, tag]⟩
    obtain ⟨observed, selected⟩ := existsResult
    obtain ⟨exitEq, valueEq, stateEq⟩ := run.deterministic (deterministic compute) (runs selected)
    exact ⟨exitEq, selected.trans (congrArg some valueEq.symm), stateEq⟩
  · rintro ⟨rfl, selected, rfl⟩
    exact runs selected

private theorem before_eval_iff (compute : Φ → Value α → Value α) (op : Φ)
    (env : Env α) (start finish : σ) (label : Nat) (value : Value α) :
    Eval (instruction compute) env (before op) start label value finish ↔
      label = 0 ∧ result? compute op env = some value ∧ finish = start :=
  observe compute op _ env start finish label value before_tag
    (fun selected => (both_run compute op env start selected).1)

theorem after_eval_iff (compute : Φ → Value α → Value α) (op : Φ)
    (env : Env α) (start finish : σ) (label : Nat) (value : Value α) :
    Eval (instruction compute) env (after op) start label value finish ↔
      label = 0 ∧ result? compute op env = some value ∧ finish = start :=
  observe compute op _ env start finish label value after_tag
    (fun selected => (both_run compute op env start selected).2)

theorem sink?_eval_iff {r r' : Region Φ} (changed : sink? r = some r')
    (compute : Φ → Value α → Value α) (env : Env α) (start finish : σ) (label : Nat)
    (value : Value α) :
    Eval (instruction compute) env r start label value finish ↔
      Eval (instruction compute) env r' start label value finish := by
  obtain ⟨op, rfl, rfl⟩ := sink?_shape.mp changed
  rw [before_eval_iff, after_eval_iff]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink
