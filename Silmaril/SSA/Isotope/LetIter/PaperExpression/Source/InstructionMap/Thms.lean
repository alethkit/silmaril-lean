module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.InstructionMap.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.InstructionMap

/-! # Fixed-bound source typing and equations under instruction relabelling -/

public section

open Silmaril

namespace Silmaril.Isotope.LetIter.PaperExpression

universe u v w r

variable {τ : Type u} {Φ : Type v} {Ψ : Type w} {ε : Type r} {φ : Φ → Ψ}

theorem Expr.mapInstr_wk (a : Expr Φ) (ξ : Nat → Nat) :
    (a.wk ξ).mapInstr φ = (a.mapInstr φ).wk ξ :=
  Source.InstructionMap.Proofs.mapInstr_wk φ a ξ

theorem Expr.mapInstr_subst (a : Expr Φ) (σ : Nat → Expr Φ) :
    (a.subst σ).mapInstr φ = (a.mapInstr φ).subst (fun i => (σ i).mapInstr φ) :=
  Source.InstructionMap.Proofs.mapInstr_subst φ a σ

variable [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ] [HasEff Φ ε] [HasEff Ψ ε]
  [Preorder ε] [Bot ε] {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b : Expr Φ}

/-- Preserving primitive endpoints and effects preserves typing at the same bound. -/
theorem Wf.mapInstr (h : Wf Γ a A e)
    (src : ∀ f, (instrSrc (φ f) : τ) = instrSrc f)
    (trg : ∀ f, (instrTrg (φ f) : τ) = instrTrg f)
    (eff : ∀ f, (instrEff (φ f) : ε) = instrEff f) :
    Wf Γ (a.mapInstr φ) A e :=
  Source.InstructionMap.Proofs.wf_map φ src trg eff h

/-- Relabelling preserves all source equations at the same bound when the
primitive endpoints and effects agree. -/
theorem Source.Eqv.mapInstr (h : Source.Eqv Γ A e a b)
    (src : ∀ f, (instrSrc (φ f) : τ) = instrSrc f)
    (trg : ∀ f, (instrTrg (φ f) : τ) = instrTrg f)
    (eff : ∀ f, (instrEff (φ f) : ε) = instrEff f) :
    Source.Eqv Γ A e (a.mapInstr φ) (b.mapInstr φ) :=
  Source.InstructionMap.Proofs.eqv_map φ src trg eff h

end Silmaril.Isotope.LetIter.PaperExpression
