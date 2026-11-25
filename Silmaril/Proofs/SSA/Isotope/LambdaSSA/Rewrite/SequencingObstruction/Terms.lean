module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionTyping
import Silmaril.Raw.SSA.Isotope.LambdaSSA.Substitution

/-! # Runtime values and instruction observations for the sequencing witness -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

abbrev Env := Semantics.Env Empty
abbrev Val := Value Empty

abbrev Typed := Resumption.Typing.ValueTyped (fun (_ _ : Empty) => False)
abbrev EnvTyped := Resumption.Typing.EnvTyped (fun (_ _ : Empty) => False)

@[expose] def prependTerm (e : Bool) : Val × Bool → Val × Bool :=
  fun (v, h) => (v, e || h)

@[expose] def term (env : Env) : Tm Instruction → Option (Val × Bool)
  | .var i => some (env i, false)
  | .op _ a => (term env a).map (fun x => (x.1, true))
  | .let₁ a b => do
    let (v, e) ← term env a
    (term (extend env v) b).map (prependTerm e)
  | .unit => some (.unit, false)
  | .pair a b => do
    let (v, e) ← term env a
    let (w, f) ← term env b
    return (.pair v w, e || f)
  | .let₂ a b => do
    let (.pair v w, e) ← term env a | none
    (term (extend (extend env v) w) b).map (prependTerm e)
  | .inl a => (term env a).map (fun (v, e) => (.inl v, e))
  | .inr a => (term env a).map (fun (v, e) => (.inr v, e))
  | .case a l r => do
    let (v, e) ← term env a
    match v with
    | .inl w => (term (extend env w) l).map (prependTerm e)
    | .inr w => (term (extend env w) r).map (prependTerm e)
    | _ => none
  | .abort _ => none

private theorem extend_rename {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) (v : Val) :
    ∀ i, extend env' v (lift ρ i) = extend env v i := by
  intro i
  cases i with
  | zero => rfl
  | succ i => exact h i

private theorem term_rename (a : Tm Instruction) {env env' : Env} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) : term env' (a.rename ρ) = term env a := by
  induction a generalizing env env' ρ with
  | var i => simp [Tm.rename, term, h]
  | op _ _ ih => simp [Tm.rename, term, ih h]
  | let₁ _ _ ia ib => simp [Tm.rename, term, ia h, ib (extend_rename h _)]
  | unit => rfl
  | pair _ _ ia ib => simp [Tm.rename, term, ia h, ib h]
  | let₂ _ _ ia ib =>
    simp only [Tm.rename, term, ia h]
    congr
    funext x
    obtain ⟨v, e⟩ := x
    cases v <;> simp [liftN, ib (extend_rename (extend_rename h _) _)]
  | inl _ ih => simp [Tm.rename, term, ih h]
  | inr _ ih => simp [Tm.rename, term, ih h]
  | case _ _ _ ia il ir =>
    simp only [Tm.rename, term, ia h]
    congr
    funext x
    obtain ⟨v, e⟩ := x
    cases v <;> simp [il (extend_rename h _), ir (extend_rename h _)]
  | abort _ _ => rfl

theorem lift_realizes {env env' : Env} {σ : Nat → Tm Instruction}
    (h : ∀ i, term env (σ i) = some (env' i, false)) (v : Val) :
    ∀ i, term (extend env v) (Tm.liftSubst σ i) = some (extend env' v i, false) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    change term (extend env v) ((σ i).rename Nat.succ) = _
    rw [term_rename _ (env := env) (ρ := Nat.succ) (fun _ => rfl)]
    exact h i

theorem term_subst (a : Tm Instruction) {env env' : Env} {σ : Nat → Tm Instruction}
    (h : ∀ i, term env (σ i) = some (env' i, false)) :
    term env (a.subst σ) = term env' a := by
  induction a generalizing env env' σ with
  | var i => exact h i
  | op _ _ ih => simp [Tm.subst, term, ih h]
  | let₁ _ _ ia ib => simp [Tm.subst, term, ia h, ib (lift_realizes h _)]
  | unit => rfl
  | pair _ _ ia ib => simp [Tm.subst, term, ia h, ib h]
  | let₂ _ _ ia ib =>
    simp only [Tm.subst, term, ia h, Tm.liftSubstN]
    congr
    funext x
    obtain ⟨v, e⟩ := x
    cases v <;> simp [ib (lift_realizes (lift_realizes h _) _)]
  | inl _ ih => simp [Tm.subst, term, ih h]
  | inr _ ih => simp [Tm.subst, term, ih h]
  | case _ _ _ ia il ir =>
    simp only [Tm.subst, term, ia h]
    congr
    funext x
    obtain ⟨v, e⟩ := x
    cases v <;> simp [il (lift_realizes h _), ir (lift_realizes h _)]
  | abort _ _ => rfl

theorem term_total {Γ : VCtx (Ty Empty)} {a : Tm Instruction} {A : Ty Empty}
    (ha : Tm.HasType Γ a A) {env : Env} (he : EnvTyped Γ env) :
    ∃ v e, term env a = some (v, e) ∧ Typed v A := by
  induction ha generalizing env with
  | var hi => exact ⟨_, _, rfl, he hi⟩
  | op _ ih =>
    obtain ⟨v, e, h, hv⟩ := ih he
    exact ⟨v, true, by simp [term, h], hv⟩
  | let₁ _ _ ia ib =>
    obtain ⟨v, e, h, hv⟩ := ia he
    obtain ⟨w, f, h', hw⟩ := ib (he.extend hv)
    exact ⟨w, e || f, by simp [term, h, h', prependTerm], hw⟩
  | unit => exact ⟨_, _, rfl, .unit⟩
  | pair _ _ ia ib =>
    obtain ⟨v, e, h, hv⟩ := ia he
    obtain ⟨w, f, h', hw⟩ := ib he
    exact ⟨.pair v w, e || f, by simp [term, h, h'], .pair hv hw⟩
  | let₂ _ _ ia ib =>
    obtain ⟨v, e, h, hv⟩ := ia he
    cases hv with
    | pair hx hy =>
      obtain ⟨w, f, h', hw⟩ := ib ((he.extend hx).extend hy)
      exact ⟨w, e || f, by simp [term, h, h', prependTerm], hw⟩
  | inl _ ih =>
    obtain ⟨v, e, h, hv⟩ := ih he
    exact ⟨.inl v, e, by simp [term, h], .inl hv⟩
  | inr _ ih =>
    obtain ⟨v, e, h, hv⟩ := ih he
    exact ⟨.inr v, e, by simp [term, h], .inr hv⟩
  | case _ _ _ ia il ir =>
    obtain ⟨v, e, h, hv⟩ := ia he
    cases hv with
    | inl hv =>
      obtain ⟨w, f, h', hw⟩ := il (he.extend hv)
      exact ⟨w, e || f, by simp [term, h, h', prependTerm], hw⟩
    | inr hv =>
      obtain ⟨w, f, h', hw⟩ := ir (he.extend hv)
      exact ⟨w, e || f, by simp [term, h, h', prependTerm], hw⟩
  | abort _ ih =>
    obtain ⟨_, _, _, hv⟩ := ih he
    cases hv

theorem term_typed {Γ : VCtx (Ty Empty)} {a : Tm Instruction} {A : Ty Empty}
    (ha : Tm.HasType Γ a A) {env : Env} (he : EnvTyped Γ env) {v : Val} {e : Bool}
    (h : term env a = some (v, e)) : Typed v A := by
  obtain ⟨w, f, h', hw⟩ := term_total ha he
  have eq : (w, f) = (v, e) := Option.some.inj (h'.symm.trans h)
  cases eq
  exact hw

theorem value_term {Γ : VCtx (Ty Empty)} {a : Tm Instruction} {A : Ty Empty}
    (ha : Tm.BranchValue Γ a A) (env : Env) : ∃ v, term env a = some (v, false) := by
  induction ha with
  | var => exact ⟨_, rfl⟩
  | unit => exact ⟨_, rfl⟩
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨v, hv⟩ := ih₁
    obtain ⟨w, hw⟩ := ih₂
    exact ⟨.pair v w, by simp [term, hv, hw]⟩
  | inl _ ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨.inl v, by simp [term, hv]⟩
  | inr _ ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨.inr v, by simp [term, hv]⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
