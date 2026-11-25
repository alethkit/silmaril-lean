module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot

/-! # Typed specialization and reconstruction at a pure unit slot -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}
variable {Γ : EffectCtx τ ε}

section Source

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {a b : Expr Φ} {C : τ} {e : ε}

omit [TypeFormers τ] in
/-- Deleting a slot preserves purity of the retained context. -/
theorem eraseCtx_pure (hΓ : Γ.Pure) (i : Nat) : (eraseCtx Γ i).Pure :=
  Proofs.eraseCtx_pure hΓ i

/-- Unit eta identifies an expression with its specialization weakened back into the original context. -/
theorem unit_eta_rebuild (i : Fin Γ.length)
    (ht : (Γ.get i).1 = unit) (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuildUnit i a) :=
  Proofs.unit_eta_rebuild i ht he ha

/-- Specializing a pure unit slot preserves typing at the original effect bound. -/
theorem wf_specializeUnit (i : Fin Γ.length) (ht : (Γ.get i).1 = unit)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (eraseCtx Γ i) (specializeUnit i a) C e :=
  Proofs.wf_specializeUnit i ht he ha

/-- Specialization at a pure unit slot characterizes source equality at the same bound. -/
theorem eqv_iff_specializeUnit (i : Fin Γ.length) (ht : (Γ.get i).1 = unit)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔ Eqv (eraseCtx Γ i) C e (specializeUnit i a) (specializeUnit i b) :=
  Proofs.eqv_iff_specializeUnit i ht he ha hb

end Source

section Native

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
variable {a b : Expr Φ} {C : τ}

/-- The pure substitution transports the entire native equality proof into the smaller context. -/
theorem native_specializeUnit (i : Fin Γ.length) (hΓ : Γ.Pure) (hty : (Γ.get i).1 = unit)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (h : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C) :
    ∃ t' s' : Tm Empty Φ (eraseCtx Γ i).length,
      (specializeUnit i a).toLetIter (eraseCtx Γ i).length = some t' ∧
      (specializeUnit i b).toLetIter (eraseCtx Γ i).length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) (eraseCtx Γ i).toBoundCtx t' s' C :=
  Proofs.native_specializeUnit i hΓ hty ht hs h

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot
