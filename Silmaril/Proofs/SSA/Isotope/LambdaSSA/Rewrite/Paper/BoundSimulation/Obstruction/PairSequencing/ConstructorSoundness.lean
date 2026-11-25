module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Defs

/-! # Evaluation of constructor-sequenced returns -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn.Beta.Constructors
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (UnitPayloadPolicy Env EnvTy Val ValTy Result)
open scoped Paper.BoundSimulation.Obstruction

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

private theorem sequence_pair (a b : Tm Φ) (env : Env) :
    evalRegionWith {} (returnOnce (.pair a b)) env =
      evalRegionWith {} (pairSequence a b) env := by
  simp only [returnOnce, pairSequence, evalRegionWith, evalTermWith,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases evalTermWith {} a env with
  | none => rfl
  | some v =>
    simp only [evalTerm_rename b (observation := {}) (env := env)
      (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    cases evalTermWith {} b env <;> rfl

private theorem sequence_inl (a : Tm Φ) (env : Env) :
    evalRegionWith {} (returnOnce (.inl a)) env =
      evalRegionWith {} (inlSequence a) env := by
  simp only [returnOnce, inlSequence, evalRegionWith, evalTermWith]
  cases evalTermWith {} a env <;> rfl

private theorem sequence_inr (a : Tm Φ) (env : Env) :
    evalRegionWith {} (returnOnce (.inr a)) env =
      evalRegionWith {} (inrSequence a) env := by
  simp only [returnOnce, inrSequence, evalRegionWith, evalTermWith]
  cases evalTermWith {} a env <;> rfl

section

set_option linter.concreteInstances false

variable [UnitPayloadPolicy]

/-- Opt-in constructor sequencing preserves the unmarked observation. -/
theorem sequencing_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.WithConstructorSequencing.Eqv Γ r s L) : SameWith {} Γ r s :=
  extension_same (observation := {}) (fun e =>
    Or.elim e unary_fusion_same (fun h => by
      cases h with
      | pair ha hb => exact fun env _ => sequence_pair _ _ env
      | inl ha => exact fun env _ => sequence_inl _ env
      | inr ha => exact fun env _ => sequence_inr _ env)) h

end

open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.AlternateUnit

private theorem value_or_empty (P : Ty α) : (∃ v, ValTy v P) ∨ Paper.StructurallyEmpty P := by
  induction P with
  | base a => exact .inl ⟨.unit, .base⟩
  | unit => exact .inl ⟨.unit, .unit⟩
  | empty => exact .inr .empty
  | product A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.pair a b, .pair ha hb⟩
      · exact .inr (.right hB)
    · exact .inr (.left hA)
  | coprod A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · exact .inl ⟨.inl a, .inl ha⟩
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.inr b, .inr hb⟩
      · exact .inr (.sum hA hB)

theorem structurallyEmpty_of_tagged_branches_eq (P : Ty α)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 (.inl (.var 0)) : Region Φ)
      (.br 0 (.inr (.var 0))) [.coprod P P]) : Paper.StructurallyEmpty P := by
  rcases value_or_empty P with ⟨v, hv⟩ | hEmpty
  · have env : EnvTy [P] (fun _ => v) := by
      intro i A hi
      cases i with
      | zero => cases Option.some.inj hi; exact hv
      | succ i => cases i <;> contradiction
    have observed := sequencing_same h (fun _ => v) env
    change Result.jump 0 (.inl v) = Result.jump 0 (.inr v) at observed
    cases observed
  · exact hEmpty

private def quote : Val → Tm Empty
  | .atom a => a.elim
  | .unit => .unit
  | .pair v w => .pair (quote v) (quote w)
  | .inl v => .inl (quote v)
  | .inr v => .inr (quote v)

private theorem eval_quote {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) (env : Env) :
    (evalTermWith {} t env).map quote = some (t.subst (quote ∘ env)) := by
  induction ht with
  | var _ => rfl
  | unit => rfl
  | pair _ _ ia ib =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ia
    obtain ⟨w, ew, hw⟩ := Option.map_eq_some_iff.mp ib
    simp [evalTermWith, ev, ew, quote, Tm.subst, hv, hw]
  | inl _ ih =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ih
    simp [evalTermWith, ev, quote, Tm.subst, hv]
  | inr _ ih =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ih
    simp [evalTermWith, ev, quote, Tm.subst, hv]

private theorem closed_subst {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) (hΓ : Γ = []) (θ : Nat → Tm Empty) : t.subst θ = t := by
  induction ht with
  | var hi => subst Γ; cases hi
  | unit => rfl
  | pair _ _ ia ib => simp only [Tm.subst, ia, ib]
  | inl _ ih => simp only [Tm.subst, ih]
  | inr _ ih => simp only [Tm.subst, ih]

private theorem singleton_branch_observation {P : Ty Empty} {Γ Δ : VCtx (Ty Empty)} {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue Γ t A) (hu : Tm.BranchValue Δ u A)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 t) (.br 0 u) [A])
    (v : Val) (hv : ValTy v P) :
    t.subst (fun _ => quote v) = u.subst (fun _ => quote v) := by
  have env : EnvTy [P] (fun _ => v) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact hv
    | succ i => cases i <;> contradiction
  have observed := sequencing_same h (fun _ => v) env
  obtain ⟨x, ex, hx⟩ := Option.map_eq_some_iff.mp (eval_quote ht (fun _ => v))
  obtain ⟨y, ey, hy⟩ := Option.map_eq_some_iff.mp (eval_quote hu (fun _ => v))
  simp only [evalRegionWith, ex, ey, Result.jump.injEq, true_and] at observed
  exact hx.symm.trans (observed ▸ hy)

theorem branch_observation_of_closed_input {t u w : Tm Empty} {A P : Ty Empty}
    (ht : Tm.BranchValue [P] t A) (hu : Tm.BranchValue [P] u A)
    (hw : Tm.BranchValue [] w P)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 t) (.br 0 u) [A]) :
    t.subst (fun _ => w) = u.subst (fun _ => w) := by
  obtain ⟨v, he, hv⟩ := Option.map_eq_some_iff.mp (eval_quote hw (fun _ => .unit))
  have typed : ValTy v P := evalTerm_typed hw.hasType (fun _ _ hi => by cases hi) he
  rw [closed_subst hw rfl] at hv
  simpa only [hv] using singleton_branch_observation ht hu h v typed

theorem closed_branch_injective {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [] t A) (hu : Tm.BranchValue [] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) : t = u := by
  simpa only [closed_subst ht rfl, closed_subst hu rfl] using
    singleton_branch_observation ht hu h .unit .unit

theorem unit_branch_observations {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [.unit] t A) (hu : Tm.BranchValue [.unit] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) :
    t.subst (fun _ => .unit) = u.subst (fun _ => .unit) ∧
      t.subst (fun _ => .inl .unit) = u.subst (fun _ => .inl .unit) :=
  ⟨singleton_branch_observation ht hu h .unit .unit,
    singleton_branch_observation ht hu h (.inl .unit) (.alternateUnit rfl)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
