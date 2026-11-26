module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Structured.Thms

/-! # Original-bound mixed reflection through the pure context cover -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.ContextProofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α]

public theorem endpoint_reflection_all_contexts {Γ : EffectCtx (Ty α) ε} {A : Ty α}
    {a b : Expr (Φ ⊕ Ψ)} (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (hΓ : Γ.Pure) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b A e)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨ContextReflection.reflect_of_atomic e e le_rfl ?_ hΓ ha hb ht hs, fun h => h.toLetIter ht hs⟩
  intro Δ slots a b t s hΔ hatoms ha hb ht hs hn
  exact (Written.endpoint_reflection_structured S T visible hΔ hatoms e ha hb ht hs).mp hn

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.ContextProofs
