module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionRouting

/-! # Divergence through the flat entry and block routers -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region
open Semantics (extend Env)
open Semantics.External (Diverges)
open SyntacticCategory (iterationBody iterationDispatch)

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop}
  {prim : Φ → Value α → σ → Prop}

local notation "Eval" => Semantics.Region.Eval
local notation "TermEval" => Semantics.Tm.Eval
local notation "TermDiverges" => Semantics.Tm.ExternalDiverges

private theorem br_diverges {env : Env α} {a : Tm Φ} {s : σ} {i : Nat} :
    Diverges instr prim (.region env (.br i a) s) ↔ TermDiverges instr prim env a s := by
  constructor
  · intro h
    cases h.unfold with
    | core h => cases h
    | br h => exact h
  · exact fun h => .fold (.br h)

private theorem let₁_diverges {env : Env α} {a : Tm Φ} {body : Region Φ} {s : σ} :
    Diverges instr prim (.region env (.let₁ a body) s) ↔
      TermDiverges instr prim env a s ∨
        ∃ v mid, TermEval instr env a s v mid ∧ Diverges instr prim (.region (extend env v) body mid) := by
  constructor
  · intro h
    cases h.unfold with
    | let₁_arg h => exact .inl h
    | core h => cases h with | let₁ run rest => exact .inr ⟨_, _, run, rest⟩
  · rintro (h | ⟨_, _, run, rest⟩)
    · exact .fold (.let₁_arg h)
    · exact .fold_core (.let₁ run rest)

private theorem let₂_diverges {env : Env α} {a : Tm Φ} {body : Region Φ} {s : σ} :
    Diverges instr prim (.region env (.let₂ a body) s) ↔
      TermDiverges instr prim env a s ∨
        ∃ v w mid, TermEval instr env a s (.pair v w) mid ∧
          Diverges instr prim (.region (extend (extend env v) w) body mid) := by
  constructor
  · intro h
    cases h.unfold with
    | let₂_arg h => exact .inl h
    | core h => cases h with | let₂ run rest => exact .inr ⟨_, _, _, run, rest⟩
  · rintro (h | ⟨_, _, _, run, rest⟩)
    · exact .fold (.let₂_arg h)
    · exact .fold_core (.let₂ run rest)

private theorem case_diverges {env : Env α} {a : Tm Φ} {left right : Region Φ} {s : σ} :
    Diverges instr prim (.region env (.case a left right) s) ↔
      TermDiverges instr prim env a s ∨
        (∃ v mid, TermEval instr env a s (.inl v) mid ∧
          Diverges instr prim (.region (extend env v) left mid)) ∨
        ∃ v mid, TermEval instr env a s (.inr v) mid ∧
          Diverges instr prim (.region (extend env v) right mid) := by
  constructor
  · intro h
    cases h.unfold with
    | case_arg h => exact .inl h
    | core h =>
      cases h with
      | case_inl run rest => exact .inr (.inl ⟨_, _, run, rest⟩)
      | case_inr run rest => exact .inr (.inr ⟨_, _, run, rest⟩)
  · rintro (h | ⟨_, _, run, rest⟩ | ⟨_, _, run, rest⟩)
    · exact .fold (.case_arg h)
    · exact .fold_core (.case_inl run rest)
    · exact .fold_core (.case_inr run rest)

private theorem diverges_lifted {k : Nat → Region Φ} {i : Nat} {env : Env α}
    {ignored payload : Value α} {s : σ} :
    Diverges instr prim (.region (extend (extend env ignored) payload) (liftLSubstVars k i) s) ↔
      Diverges instr prim (.region (extend env payload) (k i) s) :=
  Diverges.renameVars_iff (Semantics.extend_rename (fun _ => rfl) payload)

private theorem flat_bind_diverges {labels n : Nat} (r : Flat Φ labels n) (k : Nat → Region Φ)
    {env : Env α} {s : σ} :
    Diverges instr prim (.region env (r.erase.bindBranchArguments.lsubst k) s) ↔
      Diverges instr prim (.region env r.erase s) ∨
        ∃ i v mid, Eval instr env r.erase s i v mid ∧
          Diverges instr prim (.region (extend env v) (k i) mid) := by
  induction r generalizing k env s with
  | br i a =>
    change Diverges instr prim
      (.region env (.let₁ (Morphism.CaseSSA.erase a) (compLSubst labelId k i.val)) s) ↔ _
    rw [compLSubst_id_left, let₁_diverges]
    constructor
    · rintro (h | ⟨v, mid, run, rest⟩)
      · exact .inl (br_diverges.mpr h)
      · exact .inr ⟨i.val, v, mid, .br run, rest⟩
    · rintro (h | ⟨_, v, mid, run, rest⟩)
      · exact .inl (br_diverges.mp h)
      · cases run with | br run => exact .inr ⟨v, mid, run, rest⟩
  | let₁ a b ih =>
    change Diverges instr prim (.region env (.let₁ (Morphism.CaseSSA.erase a)
      (b.erase.bindBranchArguments.lsubst (liftLSubstVars k))) s) ↔ _
    rw [let₁_diverges]
    constructor
    · rintro (h | ⟨_, _, run, rest⟩)
      · exact .inl (.fold (.let₁_arg h))
      · rcases (ih _).mp rest with h | ⟨i, v, mid, body, tail⟩
        · exact .inl (.fold_core (.let₁ run h))
        · exact .inr ⟨i, v, mid, .let₁ run body, diverges_lifted.mp tail⟩
    · rintro (h | ⟨i, v, mid, run, rest⟩)
      · rcases let₁_diverges.mp h with h | ⟨val, state, arg, tail⟩
        · exact .inl h
        · exact .inr ⟨val, state, arg, (ih _).mpr (.inl tail)⟩
      · cases run with
        | let₁ arg body => exact .inr ⟨_, _, arg, (ih _).mpr (.inr ⟨i, v, mid, body, diverges_lifted.mpr rest⟩)⟩
  | let₂ a b ih =>
    change Diverges instr prim (.region env (.let₂ (Morphism.CaseSSA.erase a)
      (b.erase.bindBranchArguments.lsubst (liftLSubstVars (liftLSubstVars k)))) s) ↔ _
    rw [let₂_diverges]
    constructor
    · rintro (h | ⟨_, _, _, run, rest⟩)
      · exact .inl (.fold (.let₂_arg h))
      · rcases (ih _).mp rest with h | ⟨i, v, mid, body, tail⟩
        · exact .inl (.fold_core (.let₂ run h))
        · exact .inr ⟨i, v, mid, .let₂ run body, diverges_lifted.mp (diverges_lifted.mp tail)⟩
    · rintro (h | ⟨i, v, mid, run, rest⟩)
      · rcases let₂_diverges.mp h with h | ⟨left, right, state, arg, tail⟩
        · exact .inl h
        · exact .inr ⟨left, right, state, arg, (ih _).mpr (.inl tail)⟩
      · cases run with
        | let₂ arg body =>
          exact .inr ⟨_, _, _, arg, (ih _).mpr
            (.inr ⟨i, v, mid, body, diverges_lifted.mpr (diverges_lifted.mpr rest)⟩)⟩
  | case e l r ihl ihr =>
    change Diverges instr prim (.region env (.case (Morphism.CaseSSA.erase e)
      (l.erase.bindBranchArguments.lsubst (liftLSubstVars k))
      (r.erase.bindBranchArguments.lsubst (liftLSubstVars k))) s) ↔ _
    rw [case_diverges]
    constructor
    · rintro (h | ⟨_, _, run, rest⟩ | ⟨_, _, run, rest⟩)
      · exact .inl (.fold (.case_arg h))
      · rcases (ihl _).mp rest with h | ⟨i, v, mid, body, tail⟩
        · exact .inl (.fold_core (.case_inl run h))
        · exact .inr ⟨i, v, mid, .case_inl run body, diverges_lifted.mp tail⟩
      · rcases (ihr _).mp rest with h | ⟨i, v, mid, body, tail⟩
        · exact .inl (.fold_core (.case_inr run h))
        · exact .inr ⟨i, v, mid, .case_inr run body, diverges_lifted.mp tail⟩
    · rintro (h | ⟨i, v, mid, run, rest⟩)
      · rcases case_diverges.mp h with h | ⟨val, state, arg, tail⟩ | ⟨val, state, arg, tail⟩
        · exact .inl h
        · exact .inr (.inl ⟨val, state, arg, (ihl _).mpr (.inl tail)⟩)
        · exact .inr (.inr ⟨val, state, arg, (ihr _).mpr (.inl tail)⟩)
      · cases run with
        | case_inl arg body =>
          exact .inr (.inl ⟨_, _, arg, (ihl _).mpr (.inr ⟨i, v, mid, body, diverges_lifted.mpr rest⟩)⟩)
        | case_inr arg body =>
          exact .inr (.inr ⟨_, _, arg, (ihr _).mpr (.inr ⟨i, v, mid, body, diverges_lifted.mpr rest⟩)⟩)

private theorem packedExitArg_var_not_diverges (i : Nat) {env : Env α} {s : σ} :
    ¬ TermDiverges instr prim env (packedExitArg i (.var 0)) s := by
  induction i with
  | zero => intro h; cases h with | inl h => cases h
  | succ i ih => intro h; cases h with | inr h => exact ih h

private theorem route_comp_dispatch_not_diverges (count i : Nat) {env : Env α} {s : σ} :
    ¬ Diverges instr prim (.region env (compLSubst (routeExit count) (fun _ => iterationDispatch) i) s) := by
  rw [route_comp_dispatch, case_diverges]
  rintro (h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩)
  · by_cases hi : i < count
    · rw [ite_eq_left hi] at h
      cases h with | inr h => exact packedExitArg_var_not_diverges _ h
    · rw [ite_eq_right hi] at h
      cases h with | inl h => exact packedExitArg_var_not_diverges _ h
  · cases br_diverges.mp h
  · cases br_diverges.mp h

theorem routedFlat_body_diverges {labels n : Nat} (count : Nat) (r : Flat Φ labels n)
    {env : Env α} {s : σ} :
    Diverges instr prim (.region env (iterationBody (routedFlat count r)) s) ↔
      Diverges instr prim (.region env r.erase s) := by
  rw [iterationBody, routedFlat, lsubst_comp, flat_bind_diverges]
  constructor
  · rintro (h | ⟨i, _, _, _, rest⟩)
    · exact h
    · exact (route_comp_dispatch_not_diverges count i rest).elim
  · exact Or.inl

private theorem case_inl_var_diverges {env : Env α} {v : Value α} {left right : Region Φ} {s : σ} :
    Diverges instr prim (.region (extend env (.inl v)) (.case (.var 0) left right) s) ↔
      Diverges instr prim (.region (extend (extend env (.inl v)) v) left s) := by
  rw [case_diverges]
  constructor
  · rintro (h | ⟨_, _, run, h⟩ | ⟨_, _, run, _⟩)
    · cases h
    · cases run; exact h
    · cases run
  · exact fun h => .inr (.inl ⟨v, s, .var, h⟩)

private theorem case_inr_var_diverges {env : Env α} {v : Value α} {left right : Region Φ} {s : σ} :
    Diverges instr prim (.region (extend env (.inr v)) (.case (.var 0) left right) s) ↔
      Diverges instr prim (.region (extend (extend env (.inr v)) v) right s) := by
  rw [case_diverges]
  constructor
  · rintro (h | ⟨_, _, run, _⟩ | ⟨_, _, run, h⟩)
    · cases h
    · cases run
    · cases run; exact h
  · exact fun h => .inr (.inr ⟨v, s, .var, h⟩)

private theorem unpackExits_apply_diverges {τ : Type x} [TypeFormers τ] (L : LCtx τ)
    {i : Nat} (hi : i < L.length) (k : Nat → Region Φ) {env : Env α} {v : Value α} {s : σ} :
    Diverges instr prim (.region (extend env (packedExitValue i v)) ((unpackExits L).lsubst k) s) ↔
      Diverges instr prim (.region (extend (extend env (packedExitValue i v)) v) (k i) s) := by
  induction L generalizing i k env with
  | nil => simp at hi
  | cons A L ih =>
    cases i with
    | zero =>
      change Diverges instr prim (.region (extend env (.inl v))
        (.case (.var 0) (compLSubst labelId k 0) _) s) ↔ _
      rw [compLSubst_id_left, case_inl_var_diverges]
      rfl
    | succ i =>
      have htail : i < L.length := Nat.lt_of_succ_lt_succ hi
      rw [unpackExits, packedExitValue, Region.lsubst, lsubst_renameLabels, case_inr_var_diverges]
      exact (ih htail (liftLSubstVars k ∘ Nat.succ)).trans diverges_lifted

private theorem unpackExits_comp_diverges {τ : Type x} [TypeFormers τ] (L : LCtx τ)
    {i : Nat} (hi : i < L.length) (k : Nat → Region Φ) {env : Env α} {v : Value α} {s : σ} :
    Diverges instr prim (.region (extend env (packedExitValue i v))
      (compLSubst (fun _ => unpackExits L) k 0) s) ↔
      Diverges instr prim (.region (extend env v) (k i) s) :=
  (unpackExits_apply_diverges L hi (liftLSubstVars k)).trans diverges_lifted

theorem dispatcherBody_diverges_at {τ : Type x} [TypeFormers τ] [HasTy Φ τ]
    {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ} {g : FiniteCFG Φ blocks exits 0}
    (hg : FiniteCFG.HasType .nil R E g) {i : Nat} (hi : i < blocks)
    {env : Env α} {v : Value α} {s : σ} :
    Diverges instr prim (.region (extend env (packedExitValue i v))
        (iterationBody (packedDispatcherRegion hg)) s) ↔
      Diverges instr prim (.region (extend env v) (g.block ⟨i, hi⟩).erase s) := by
  rw [iterationBody_packedDispatcher, unpackExits_comp_diverges (List.ofFn R) (i := i) (by simpa using hi),
    packedBlockContinuations_at hg hi, routedFlat_body_diverges]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution
