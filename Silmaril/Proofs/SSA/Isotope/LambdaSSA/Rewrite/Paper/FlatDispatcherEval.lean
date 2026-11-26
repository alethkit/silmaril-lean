module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

/-! # Finite execution of a routed flat region -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region
open Semantics (extend Env)

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

local notation "Eval" => Semantics.Region.Eval

private theorem eval_lifted {k : Nat → Region Φ} {i label : Nat} {env : Env α}
    {ignored payload out : Value α} {s t : σ} :
    Eval instr (extend (extend env ignored) payload) (liftLSubstVars k i) s label out t ↔
      Eval instr (extend env payload) (k i) s label out t :=
  Semantics.Region.Eval.renameVars_iff (Semantics.extend_rename (fun _ => rfl) payload)

theorem flat_bind_eval {labels n : Nat} (r : Flat Φ labels n) (k : Nat → Region Φ)
    {env : Env α} {s t : σ} {label : Nat} {out : Value α} :
    Eval instr env (r.erase.bindBranchArguments.lsubst k) s label out t ↔
      ∃ i v m, Eval instr env r.erase s i v m ∧ Eval instr (extend env v) (k i) m label out t := by
  induction r generalizing k env s t label out with
  | br i a =>
    change Eval instr env (.let₁ (Morphism.CaseSSA.erase a) (compLSubst labelId k i.val)) s label out t ↔ _
    rw [compLSubst_id_left]
    constructor
    · intro h
      cases h with
      | let₁ ha hb => exact ⟨i.val, _, _, .br ha, hb⟩
    · rintro ⟨i, v, m, h, hk⟩
      cases h with
      | br ha => exact .let₁ ha hk
  | let₁ a b ih =>
    constructor
    · intro h
      cases h with
      | let₁ ha hb =>
        obtain ⟨i, v, m, he, hk⟩ := (ih _).mp hb
        exact ⟨i, v, m, .let₁ ha he, eval_lifted.mp hk⟩
    · rintro ⟨i, v, m, h, hk⟩
      cases h with
      | let₁ ha hb => exact .let₁ ha ((ih _).mpr ⟨i, v, m, hb, eval_lifted.mpr hk⟩)
  | let₂ a b ih =>
    constructor
    · intro h
      cases h with
      | let₂ ha hb =>
        obtain ⟨i, v, m, he, hk⟩ := (ih _).mp hb
        exact ⟨i, v, m, .let₂ ha he, eval_lifted.mp (eval_lifted.mp hk)⟩
    · rintro ⟨i, v, m, h, hk⟩
      cases h with
      | let₂ ha hb =>
        exact .let₂ ha ((ih _).mpr ⟨i, v, m, hb, eval_lifted.mpr (eval_lifted.mpr hk)⟩)
  | case e l r ihl ihr =>
    constructor
    · intro h
      cases h with
      | case_inl he hl =>
        obtain ⟨i, v, m, h, hk⟩ := (ihl _).mp hl
        exact ⟨i, v, m, .case_inl he h, eval_lifted.mp hk⟩
      | case_inr he hr =>
        obtain ⟨i, v, m, h, hk⟩ := (ihr _).mp hr
        exact ⟨i, v, m, .case_inr he h, eval_lifted.mp hk⟩
    · rintro ⟨i, v, m, h, hk⟩
      cases h with
      | case_inl he h => exact .case_inl he ((ihl _).mpr ⟨i, v, m, h, eval_lifted.mpr hk⟩)
      | case_inr he h => exact .case_inr he ((ihr _).mpr ⟨i, v, m, h, eval_lifted.mpr hk⟩)

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

theorem eval_routeExit {env : Semantics.Env α} {payload result : Value α}
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
  rw [routedFlat, flat_bind_eval]
  constructor
  · rintro ⟨i, v, m, run, route⟩
    obtain ⟨hl, hv, rfl⟩ := eval_routeExit.mp route
    exact ⟨i, v, run, hl, hv⟩
  · rintro ⟨i, v, run, hl, hv⟩
    exact ⟨i, v, finish, run, eval_routeExit.mpr ⟨hl, hv, rfl⟩⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher
