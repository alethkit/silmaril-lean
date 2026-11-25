module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.InstructionMap.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs

/-! # Fixed-bound typing and equation preservation under instruction relabelling -/

open Silmaril

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.InstructionMap.Proofs

universe u v w r

variable {τ : Type u} {Φ : Type v} {Ψ : Type w} {ε : Type r} (φ : Φ → Ψ)

public theorem mapInstr_wk (a : Expr Φ) (ξ : Nat → Nat) :
    (a.wk ξ).mapInstr φ = (a.mapInstr φ).wk ξ := by
  induction a generalizing ξ <;> simp [Expr.wk, Expr.mapInstr, *]

private theorem mapInstr_liftSubst (σ : Nat → Expr Φ) :
    (fun i => (Expr.liftSubst σ i).mapInstr φ) =
      Expr.liftSubst (fun i => (σ i).mapInstr φ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact mapInstr_wk φ (σ i) Nat.succ

public theorem mapInstr_subst (a : Expr Φ) (σ : Nat → Expr Φ) :
    (a.subst σ).mapInstr φ = (a.mapInstr φ).subst (fun i => (σ i).mapInstr φ) := by
  induction a generalizing σ <;> simp [Expr.subst, Expr.mapInstr, mapInstr_liftSubst, *]

private theorem mapInstr_subst0 (a : Expr Φ) :
    (fun i => (a.subst0 i).mapInstr φ) = (a.mapInstr φ).subst0 := by
  funext i
  cases i <;> rfl

private theorem map_rewrite {a b : Expr Φ} (h : Rewrite a b) :
    Rewrite (a.mapInstr φ) (b.mapInstr φ) := by
  cases h with
  | let1_op f a b =>
    simpa only [Expr.mapInstr, Expr.wk1, mapInstr_wk] using
      Rewrite.let1_op (φ f) (a.mapInstr φ) (b.mapInstr φ)
  | let1_let1 a b c =>
    simpa only [Expr.mapInstr, Expr.wk1, mapInstr_wk] using
      Rewrite.let1_let1 (a.mapInstr φ) (b.mapInstr φ) (c.mapInstr φ)
  | let1_let2 a b c =>
    simpa only [Expr.mapInstr, Expr.wk1, mapInstr_wk] using
      Rewrite.let1_let2 (a.mapInstr φ) (b.mapInstr φ) (c.mapInstr φ)
  | let1_case a l r b =>
    simpa only [Expr.mapInstr, Expr.wk1, mapInstr_wk] using
      Rewrite.let1_case (a.mapInstr φ) (l.mapInstr φ) (r.mapInstr φ) (b.mapInstr φ)
  | let1_abort a b =>
    simpa only [Expr.mapInstr, Expr.wk1, mapInstr_wk] using
      Rewrite.let1_abort (a.mapInstr φ) (b.mapInstr φ)
  | let2_eta a => exact .let2_eta _
  | let2_pair a b c =>
    simpa only [Expr.mapInstr, Expr.wk0, mapInstr_wk] using
      Rewrite.let2_pair (a.mapInstr φ) (b.mapInstr φ) (c.mapInstr φ)
  | let1_eta a => exact .let1_eta _
  | let2_bind a b =>
    simpa only [Expr.mapInstr, Expr.wk2, mapInstr_wk] using
      Rewrite.let2_bind (a.mapInstr φ) (b.mapInstr φ)
  | case_bind a l r =>
    simpa only [Expr.mapInstr, Expr.wk1, mapInstr_wk] using
      Rewrite.case_bind (a.mapInstr φ) (l.mapInstr φ) (r.mapInstr φ)
  | case_eta a => exact .case_eta _

private theorem map_reduce {a b : Expr Φ} (h : Reduce a b) :
    Reduce (a.mapInstr φ) (b.mapInstr φ) := by
  cases h with
  | case_inl => exact .case_inl _ _ _
  | case_inr => exact .case_inr _ _ _

variable [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ] [HasEff Φ ε] [HasEff Ψ ε]
  [Preorder ε] [Bot ε]
  (src : ∀ f, (instrSrc (φ f) : τ) = instrSrc f)
  (trg : ∀ f, (instrTrg (φ f) : τ) = instrTrg f)
  (eff : ∀ f, (instrEff (φ f) : ε) = instrEff f)
  {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b : Expr Φ}

include src trg eff

public theorem wf_map (h : Wf Γ a A e) : Wf Γ (a.mapInstr φ) A e := by
  induction h with
  | var i hi => exact .var i hi
  | @op Γ f a e hf ha ih =>
    exact trg f ▸ Wf.op (f := φ f) (by simpa only [eff] using hf) (by simpa only [src] using ih)
  | let₁ ha hb iha ihb => exact .let₁ iha ihb
  | pair ha hb iha ihb => exact .pair iha ihb
  | unit Γ e => exact .unit Γ e
  | let₂ ha hb iha ihb => exact .let₂ iha ihb
  | inl ha ih => exact .inl ih
  | inr hb ih => exact .inr ih
  | case ha hl hr iha ihl ihr => exact .case iha ihl ihr
  | abort ha ih => exact .abort ih

private theorem step_map (h : Step Γ A e a b) :
    Step Γ A e (a.mapInstr φ) (b.mapInstr φ) := by
  cases h with
  | let1_beta ha hb =>
    simpa only [Expr.mapInstr, mapInstr_subst, mapInstr_subst0] using
      Step.let1_beta (wf_map φ src trg eff ha) (wf_map φ src trg eff hb)
  | rewrite ha hb h =>
    exact .rewrite (wf_map φ src trg eff ha) (wf_map φ src trg eff hb) (map_rewrite φ h)
  | reduce ha hb h =>
    exact .reduce (wf_map φ src trg eff ha) (wf_map φ src trg eff hb) (map_reduce φ h)
  | initial hΓ ha hb => exact .initial hΓ (wf_map φ src trg eff ha) (wf_map φ src trg eff hb)
  | terminal ha hb => exact .terminal (wf_map φ src trg eff ha) (wf_map φ src trg eff hb)

public theorem eqv_map (h : Eqv Γ A e a b) :
    Eqv Γ A e (a.mapInstr φ) (b.mapInstr φ) := by
  induction h with
  | step h => exact .step (step_map φ src trg eff h)
  | refl h => exact .refl (wf_map φ src trg eff h)
  | symm h ih => exact .symm ih
  | trans h h' ih ih' => exact .trans ih ih'
  | @op Γ e f a b hf h ih =>
    exact trg f ▸ Eqv.op (f := φ f) (by simpa only [eff] using hf) (by simpa only [src] using ih)
  | let1 ha hb iha ihb => exact .let1 iha ihb
  | pair ha hb iha ihb => exact .pair iha ihb
  | let2 ha hb iha ihb => exact .let2 iha ihb
  | inl ha ih => exact .inl ih
  | inr hb ih => exact .inr ih
  | case ha hl hr iha ihl ihr => exact .case iha ihl ihr
  | abort ha ih => exact .abort ih

end Silmaril.Isotope.LetIter.PaperExpression.Source.InstructionMap.Proofs
