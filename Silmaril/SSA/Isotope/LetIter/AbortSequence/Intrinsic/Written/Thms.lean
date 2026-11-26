module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Context.Thms

/-! # Intrinsic native classes of written SSA expressions -/

public section

open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic

universe u v r

/-- A successful lowering of a typed expression inhabits the corresponding
native fiber at the original upper bound. -/
@[expose] def ofLowering {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a : Expr Φ} (ha : Wf Γ a A e)
    {t : Tm Empty Φ Γ.length} (ht : a.toLetIter Γ.length = some t) :
    Term Φ (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A e :=
  ⟨t, let ⟨_, hl, typed⟩ := ha.toLetIter; Option.some.inj (hl.symm.trans ht) ▸ typed⟩

/-- At any discrete source signature, written equations descend to the native
classes at the same effect bound and with bottom as the purity test. -/
theorem abortClass_ofLowering_eq_of_eqv
    {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    {Γ : EffectCtx τ ε} {A : τ} {e : ε} {a b : Expr Φ}
    (ha : Wf Γ a A e) (hb : Wf Γ b A e)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (h : Eqv Γ A e a b) :
    abortClass (⊥ : ε) (ofLowering ha ht) = abortClass (⊥ : ε) (ofLowering hb hs) :=
  abortClass_eq_iff.mpr (h.toLetIter ht hs)

/-- In the mixed signature, written equality at the original effect bound is
exactly equality of the lowered classes. Inputs may have any source type and
must have bottom annotations. Sum-response instructions must be nonpure. -/
theorem abortClass_ofLowering_eq_iff
    {α Φ Ψ : Type u} (S : FreeTree.Signature α Φ) (T : SumSignature α Ψ)
    {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    [DecidableEq α] {Γ : EffectCtx (Ty α) ε} {A : Ty α} {e : ε} {a b : Expr (Φ ⊕ Ψ)}
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (hΓ : Γ.Pure)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b A e)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    abortClass (⊥ : ε) (ofLowering ha ht) = abortClass (⊥ : ε) (ofLowering hb hs) ↔ Eqv Γ A e a b := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  exact abortClass_eq_iff.trans
    (Response.Mixed.Written.endpoint_reflection_all_contexts S T visible hΓ e ha hb ht hs)

end Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic
