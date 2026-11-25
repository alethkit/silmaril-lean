module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit

/-! # Typed product-slot splitting at the original effect bound -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ProductSplit

universe u v w
variable {τ : Type u} {Φ : Type v} {ε : Type w}

section Source

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {Γ : EffectCtx τ ε} {A B C : τ} {e : ε} {a b : Expr Φ}

omit [TypeFormers τ] in
/-- Splitting a product preserves a pure context. -/
theorem splitCtx_pure (hΓ : Γ.Pure) (i : Fin Γ.length) (A B : τ) :
    (splitCtx Γ i A B).Pure :=
  Proofs.splitCtx_pure hΓ i A B

/-- Rebuild the original expression by a pair let on the selected product slot. -/
theorem eqv_rebuild (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuild i a) :=
  Proofs.eqv_rebuild i ht he ha

/-- Specialization preserves the source result type and effect bound. -/
theorem wf_split (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (splitCtx Γ i A B) (split i a) C e :=
  Proofs.wf_split i ht he ha

/-- Equality in the specialized context characterizes original-bound source equality. -/
theorem eqv_iff_split (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔ Eqv (splitCtx Γ i A B) C e (split i a) (split i b) :=
  Proofs.eqv_iff_split i ht he ha hb

end Source

section Native

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
variable {Γ : EffectCtx τ ε} {A B C : τ} {a b : Expr Φ}

/-- Pure typed substitution transports the native equality into the split context. -/
theorem native_split (i : Fin Γ.length) (hΓ : Γ.Pure) (hty : (Γ.get i).1 = product A B)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (h : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C) :
    ∃ t' s' : Tm Empty Φ (splitCtx Γ i A B).length,
      (split i a).toLetIter (splitCtx Γ i A B).length = some t' ∧
      (split i b).toLetIter (splitCtx Γ i A B).length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) (splitCtx Γ i A B).toBoundCtx t' s' C :=
  Proofs.native_split i hΓ hty ht hs h

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.ProductSplit
