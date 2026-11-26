module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Normalize

/-! # Original-bound reflection for well-typed written mixed expressions -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} {c : α} {a b : Expr (Φ ⊕ Ψ)}

/-- Normalize a written expression at any result type to a finite request
tree with typed constructor values at its return leaves. -/
theorem normalize {A : Ty α} (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∃ p : Code S T A ss, p.WellTyped S T e ∧ Eqv Γ A e a p.source :=
  Proofs.normalize S T hΓ hs e ha

/-- The mixed signature and a pure atomic input context admit no written
computation of empty result. -/
theorem not_wf_empty (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ¬ Wf Γ a .empty e := by
  intro h
  obtain ⟨p, _, _⟩ := normalize S T hΓ hs e h
  exact Proofs.no_empty_code S T p

/-- Normalize written syntax compositionally at its typing bound. Intermediate
leaves carry constructor values, so a retained sum can pass through a product
or let before its tag is inspected. -/
theorem normalize_atomic (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a (.base c) e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∃ p : Mixed.Program S T c ss, p.WellTyped S T e ∧ Eqv Γ (.base c) e a p.source :=
  Proofs.normalize_atomic S T hΓ hs e ha

variable [EffectIteration ε] [DecidableEq α]

/-- Exact conservativity on written endpoints at their original effect
bound. Both terms may have effectful compound intermediate results. -/
theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a (.base c) e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b (.base c) e)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hu : b.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔ Eqv Γ (.base c) e a b :=
  Proofs.endpoint_reflection S T visible hΓ hs e ha hb ht hu

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written
