module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms
import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat.Capture
open LambdaSSA
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Region.InputDestructure
open LetCase.LocallyNameless (Tm)

universe u v w x

variable {τ : Type u} {F : Type v} {α : Type w} {σ : Type x}
variable {instr : F → Value α → σ → Value α → σ → Prop}
variable {env env' : Env α} {s t : σ} {n labels out : Nat} {value : Value α}

local notation "Eval" => Semantics.Region.Eval
local notation "ExprEval" => Semantics.Tm.Eval

private theorem extend_agrees (h : ∀ i : Fin n, env i.val = env' i.val) (v : Value α) :
    ∀ i : Fin (n + 1), extend env v i.val = extend env' v i.val :=
  Fin.cases rfl h

private theorem expr_env_iff {a : Tm Empty F n}
    (agree : ∀ i : Fin n, env i.val = env' i.val) :
    ExprEval instr env (Morphism.CaseSSA.erase a) s value t ↔
      ExprEval instr env' (Morphism.CaseSSA.erase a) s value t :=
  (Morphism.CaseSSA.erase_caseEval_iff (fun _ => rfl)).trans
    (Morphism.CaseSSA.erase_caseEval_iff (fun i => (agree i).symm)).symm

private theorem flat_env {a : Flat F labels n}
    (agree : ∀ i : Fin n, env i.val = env' i.val)
    (run : Eval instr env a.erase s out value t) : Eval instr env' a.erase s out value t := by
  induction a generalizing env env' s t out value with
  | br i arg =>
    cases run with
    | br ha => exact .br ((expr_env_iff agree).mp ha)
  | let₁ op rest ih =>
    cases run with
    | let₁ ha hb => exact .let₁ ((expr_env_iff agree).mp ha) (ih (extend_agrees agree _) hb)
  | let₂ op rest ih =>
    cases run with
    | let₂ ha hb =>
      exact .let₂ ((expr_env_iff agree).mp ha) (ih (extend_agrees (extend_agrees agree _) _) hb)
  | case op l r ihl ihr =>
    cases run with
    | case_inl ha hb => exact .case_inl ((expr_env_iff agree).mp ha) (ihl (extend_agrees agree _) hb)
    | case_inr ha hb => exact .case_inr ((expr_env_iff agree).mp ha) (ihr (extend_agrees agree _) hb)

private theorem flat_env_iff {a : Flat F labels n}
    (agree : ∀ i : Fin n, env i.val = env' i.val) :
    Eval instr env a.erase s out value t ↔ Eval instr env' a.erase s out value t :=
  ⟨flat_env agree, flat_env (fun i => (agree i).symm)⟩

/-- The environment after the decoder splits the given capture values. -/
private def decoded : Nat → Env α → Env α → Env α
  | 0, _, ambient => ambient
  | n + 1, env, ambient =>
    decoded n (env ∘ Nat.succ) (extend (extend ambient (packEnv n (env ∘ Nat.succ))) (env 0))

private theorem decoded_retained (Γ : List τ) (original ambient : Env α) (i : Nat) :
    decoded Γ.length original ambient (retained Γ i) = ambient i := by
  induction Γ generalizing i original ambient with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.length_cons, retained, decoded, ih, Semantics.extend_succ]

private theorem decoded_field (Γ : List τ) (original ambient : Env α) {i : Nat}
    (hi : i < Γ.length) : decoded Γ.length original ambient (field Γ i) = original i := by
  induction Γ generalizing i original ambient with
  | nil => simp at hi
  | cons A Γ ih =>
    cases i with
    | zero => simp only [List.length_cons, decoded, field, decoded_retained, Semantics.extend_zero]
    | succ i => exact ih _ _ (Nat.lt_of_succ_lt_succ hi)

private theorem var_eval {i : Nat} (h : ExprEval instr env (.var i) s value t) :
    value = env i ∧ t = s := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem split_eval_iff (Γ : List τ) (i : Nat) (original ambient : Env α)
    (packet : ambient i = packEnv Γ.length original) {r : Region F} :
    Eval instr ambient (split Γ i r) s out value t ↔
      Eval instr (decoded Γ.length original ambient) r s out value t := by
  induction Γ generalizing i original ambient with
  | nil => rfl
  | cons A Γ ih =>
    let tail := packEnv Γ.length (original ∘ Nat.succ)
    let next := extend (extend ambient tail) (original 0)
    have evalVar : ExprEval instr ambient (.var i) s (.pair tail (original 0)) s :=
      .var_of_eq packet
    have rest := ih 1 (original ∘ Nat.succ) next (show next 1 = tail from rfl)
    constructor
    · intro h
      cases h with
      | let₂ ha hb =>
        obtain ⟨fields, rfl⟩ := var_eval ha
        obtain ⟨rfl, rfl⟩ := Value.pair.inj (fields.trans packet)
        exact rest.mp hb
    · intro h
      exact .let₂ evalVar (rest.mpr h)

private theorem decode_entry_iff {a : Flat F labels n} (Γ : List τ) (length : Γ.length = n)
    (packet : env' 0 = packEnv n env) :
    Eval instr env' (a.erase.packInputsDestructure Γ) s out value t ↔
      Eval instr env a.erase s out value t := by
  unfold Region.packInputsDestructure
  refine (split_eval_iff Γ 0 env env' (length.symm ▸ packet)).trans ?_
  refine (Semantics.Region.Eval.renameVars_iff (fun _ => rfl)).trans (flat_env_iff ?_)
  intro i
  exact decoded_field Γ env env' (length.symm ▸ i.isLt)

variable {blocks exits : Nat}
variable {β : BoundCtx τ n} {input : Tm Empty F 0}
variable {g : FiniteCFG F blocks exits n} {closed : FiniteCFG F blocks exits 0}

theorem entry_eval_iff (h : Closes β input g closed)
    (packet : ∀ v state, ExprEval instr env' (Morphism.CaseSSA.erase input) s v state ↔
      v = packEnv n env ∧ state = s) :
    Eval instr env' closed.entry.erase s out value t ↔ Eval instr env g.entry.erase s out value t := by
  rw [h.entry]
  have decode := decode_entry_iff (instr := instr) (a := g.entry) (s := s) (t := t)
    (out := out) (value := value) β.toList (BoundCtx.length_toList β)
    (env := env) (env' := extend env' (packEnv n env)) rfl
  constructor
  · intro run
    cases run with
    | let₁ ha hb =>
      obtain ⟨rfl, rfl⟩ := (packet _ _).mp ha
      exact decode.mp hb
  · intro run
    exact .let₁ ((packet _ _).mpr ⟨rfl, rfl⟩) (decode.mpr run)

theorem graph_eval_iff (h : Closes β input g closed)
    (packet : ∀ v state, ExprEval instr env' (Morphism.CaseSSA.erase input) s v state ↔
      v = packEnv n env ∧ state = s) :
    Eval instr env' closed.erase s out value t ↔ Eval instr env g.erase s out value t := by
  have blockEval (i : Fin blocks) (arg : Value α) {s' t' : σ} {label : Nat} {v : Value α} :
      Eval instr (extend env' arg) (closed.block i).erase s' label v t' ↔
        Eval instr (extend env arg) (g.block i).erase s' label v t' := by
    rw [← h.block i]
    exact flat_env_iff (Fin.cases rfl (fun i => i.elim0))
  constructor
  · intro run
    cases run with
    | cfg entry follow =>
      exact .cfg ((entry_eval_iff h packet).mp entry)
        (follow.map_block fun i arg => (blockEval i arg).mp)
  · intro run
    cases run with
    | cfg entry follow =>
      exact .cfg ((entry_eval_iff h packet).mpr entry)
        (follow.map_block fun i arg => (blockEval i arg).mpr)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture
