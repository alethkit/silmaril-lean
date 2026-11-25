module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Typing

/-! # Typing the written SSA expression fragment in LetIter -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression

open LocallyNameless (Tm HasTypeEffect Pure)

variable {τ : Type u} {Φ : Type v} {ε : Type w}

/-- Bound-context lookup agrees with the projected newest-first source slot. -/
theorem EffectCtx.get_toBoundCtx (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    Γ.toBoundCtx.get i = (Γ.get i).1 :=
  Proofs.EffectCtx.get_toBoundCtx Γ i

section Comparison

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {a : Expr Φ} {e : ε} {A : τ}

/-- The bound on an expression is preserved when erasing ambient slot effects. -/
theorem Wf.toLetIter (h : Wf Γ a A e) :
    ∃ t, a.toLetIter Γ.length = some t ∧ HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx t A e :=
  Proofs.Wf.toLetIter h

/-- Translating a bottom-effect source expression gives a syntactically pure term. -/
theorem Wf.pure_toLetIter (h : Wf Γ a A (⊥ : ε)) {t : Tm Empty Φ Γ.length}
    (lowered : a.toLetIter Γ.length = some t) : Pure (⊥ : ε) t :=
  Proofs.Wf.pure_toLetIter h lowered

/-- Translation reflects exact typing at the same effect bound in a pure context. -/
theorem Wf.ofLetIter {t : Tm Empty Φ Γ.length} (pureCtx : Γ.Pure)
    (lowered : a.toLetIter Γ.length = some t)
    (typed : HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx t A e) :
    Wf Γ a A e :=
  Proofs.Wf.ofLetIter pureCtx lowered typed

/-- Typing at each effect bound agrees on pure contexts, including scoping. -/
theorem wf_iff_hasTypeEffect (pureCtx : Γ.Pure) :
    Wf Γ a A e ↔
      ∃ t, a.toLetIter Γ.length = some t ∧ HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx t A e :=
  ⟨Wf.toLetIter, fun ⟨_, lowered, typed⟩ => Wf.ofLetIter pureCtx lowered typed⟩

end Comparison

end Silmaril.Isotope.LetIter.PaperExpression
