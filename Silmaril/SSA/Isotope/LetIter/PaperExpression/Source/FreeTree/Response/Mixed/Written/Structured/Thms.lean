module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Structured.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Structured

/-! # Original-bound reflection at a structured result -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {A : Ty α}

theorem valueDenote_injective {n : Nat} {ss : Fin n → α} :
    Function.Injective (valueDenote S ss Tree.var (A := A)) :=
  StructuredProofs.valueDenote_injective S

theorem Code.lowers {n : Nat} {ss : Fin n → α} (p : Code S T A ss) :
    p.source.toLetIter n = some p.native :=
  StructuredProofs.lowers S T p

/-- Equality at every free-tree valuation recovers the full request tree and
its typed constructor leaves. -/
theorem Code.eq_of_denote_eq {n : Nat} {ss : Fin n → α} {p q : Code S T A ss}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (ss i)),
      p.denote S T modelSlots vars = q.denote S T modelSlots vars) : p = q :=
  StructuredProofs.eq_of_denote_eq S T h

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

/-- Native interpretation follows each request and returns its structured value. -/
theorem Code.eval_exists {m : Nat} (modelSlots : Fin m → α)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Code S T A slots) (hp : p.WellTyped S T e) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx p.native A,
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) (variableEnv S modelSlots hs vars) = p.denote S T modelSlots vars :=
  StructuredProofs.eval_exists S T modelSlots hs e p hp

variable [DecidableEq α]

theorem Code.native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Code S T A slots) (hp : p.WellTyped S T e) (hq : q.WellTyped S T e)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx p.native q.native A) : p = q :=
  StructuredProofs.native_eq_implies_eq S T visible hs e p q hp hq hn

variable [EffectIteration ε]

/-- Original-bound conservativity for written expressions of any result
type in the existing mixed signature and a pure atomic input context. -/
theorem endpoint_reflection_structured {a b : Expr (Φ ⊕ Ψ)}
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b A e)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hu : b.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b :=
  StructuredProofs.endpoint_reflection_structured S T visible hΓ hs e ha hb ht hu

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written
