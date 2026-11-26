module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher

/-! # Finite execution of a routed flat region -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

local notation "Eval" => Semantics.Region.Eval

private theorem packedExitArg_subst (i : Nat) (a : Tm Φ) (θ : Nat → Tm Φ) :
    (packedExitArg i a).subst θ = packedExitArg i (a.subst θ) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [packedExitArg, Tm.subst, ih]

private theorem routeExit_subst_self (blocks i : Nat) :
    (routeExit (Φ := Φ) blocks i).substVars (Tm.singleSubst (.var 0)) = routeExit blocks i := by
  simp only [routeExit]
  split <;> simp only [Region.substVars, Tm.subst, packedExitArg_subst] <;> rfl

private theorem routedFlat_br {labels n : Nat} (blocks : Nat) (i : Fin labels)
    (a : LetCase.LocallyNameless.Tm Empty Φ n) :
    routedFlat blocks (.br i a) = .let₁ (Morphism.CaseSSA.erase a) (routeExit blocks i.val) := by
  simp only [routedFlat, Flat.erase, bindBranchArguments, Region.lsubst, liftLSubstVars_routeExit,
    routeExit_subst_self]

private theorem packedExitArg_var_eval {env : Semantics.Env α} {i : Nat} {s finish : σ}
    {out : Value α}
    (h : Semantics.Tm.Eval instr env (packedExitArg i (.var 0)) s out finish) :
    out = packedExitValue i (env 0) ∧ finish = s := by
  induction i generalizing out with
  | zero =>
    cases h with
    | inl h => cases h; exact ⟨rfl, rfl⟩
  | succ i ih =>
    cases h with
    | inr h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩

private theorem eval_routeExit {env : Semantics.Env α} {payload result : Value α}
    {blocks i label : Nat} {state finish : σ} :
    Eval instr (Semantics.extend env payload) (routeExit blocks i) state label result finish ↔
      label = 0 ∧ result = routeValue blocks i payload ∧ finish = state := by
  by_cases h : i < blocks
  · simp only [routeExit, routeValue, ite_eq_left h]
    constructor
    · intro h
      cases h with
      | br h => cases h with
        | inr h => obtain ⟨rfl, rfl⟩ := packedExitArg_var_eval h; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact .br (.inr (packedExitArg_eval (.var (i := 0)) i))
  · simp only [routeExit, routeValue, ite_eq_right h]
    constructor
    · intro h
      cases h with
      | br h => cases h with
        | inl h => obtain ⟨rfl, rfl⟩ := packedExitArg_var_eval h; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact .br (.inl (packedExitArg_eval (.var (i := 0)) (i - blocks)))

theorem routedFlat_eval_iff {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n)
    {env : Semantics.Env α} {s finish : σ} {label : Nat} {out : Value α} :
    Eval instr env (routedFlat blocks r) s label out finish ↔
      ∃ i payload, Eval instr env r.erase s i payload finish ∧
        label = 0 ∧ out = routeValue blocks i payload := by
  induction r generalizing env s finish label out with
  | br i a =>
    rw [routedFlat_br]
    constructor
    · intro h
      cases h with
      | let₁ ha hb =>
        obtain ⟨rfl, rfl, rfl⟩ := eval_routeExit.mp hb
        exact ⟨i.val, _, .br ha, rfl, rfl⟩
    · rintro ⟨_, _, h, rfl, rfl⟩
      cases h with
      | br ha => exact .let₁ ha (eval_routeExit.mpr ⟨rfl, rfl, rfl⟩)
  | let₁ a b ih =>
    simp only [routedFlat, Flat.erase, bindBranchArguments, Region.lsubst, liftLSubstVars_routeExit] at *
    constructor
    · intro h
      cases h with
      | let₁ ha hb =>
        obtain ⟨i, payload, hb, hl, hv⟩ := ih.mp hb
        exact ⟨i, payload, .let₁ ha hb, hl, hv⟩
    · rintro ⟨_, _, h, hl, hv⟩
      cases h with
      | let₁ ha hb => exact .let₁ ha (ih.mpr ⟨_, _, hb, hl, hv⟩)
  | let₂ a b ih =>
    simp only [routedFlat, Flat.erase, bindBranchArguments, Region.lsubst, liftLSubstVars_routeExit] at *
    constructor
    · intro h
      cases h with
      | let₂ ha hb =>
        obtain ⟨i, payload, hb, hl, hv⟩ := ih.mp hb
        exact ⟨i, payload, .let₂ ha hb, hl, hv⟩
    · rintro ⟨_, _, h, hl, hv⟩
      cases h with
      | let₂ ha hb => exact .let₂ ha (ih.mpr ⟨_, _, hb, hl, hv⟩)
  | case a l r ihl ihr =>
    simp only [routedFlat, Flat.erase, bindBranchArguments, Region.lsubst, liftLSubstVars_routeExit] at *
    constructor
    · intro h
      cases h with
      | case_inl ha hl =>
        obtain ⟨i, payload, h, hl, hv⟩ := ihl.mp hl
        exact ⟨i, payload, .case_inl ha h, hl, hv⟩
      | case_inr ha hr =>
        obtain ⟨i, payload, h, hl, hv⟩ := ihr.mp hr
        exact ⟨i, payload, .case_inr ha h, hl, hv⟩
    · rintro ⟨_, _, h, hl, hv⟩
      cases h with
      | case_inl ha h => exact .case_inl ha (ihl.mpr ⟨_, _, h, hl, hv⟩)
      | case_inr ha h => exact .case_inr ha (ihr.mpr ⟨_, _, h, hl, hv⟩)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher
