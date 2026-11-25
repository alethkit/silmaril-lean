module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Equations.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Native
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Native.Rewrites

/-! # Lowering the fixed-effect source equations into the abort-extended theory -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

open LocallyNameless (Tm HasType HasTypeEffect AbortEquiv)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- The native form of source `Rewrite.let1_abort`. The empty scrutinee and
continuation may both be effectful. -/
theorem commute_abort {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    {c : Tm Empty Φ (n + 1)} {X A : τ} {pe : ε}
    (ht : HasType Φ (Ctx.nil : Ctx Empty τ) β t empty)
    (hc : HasType Φ (Ctx.nil : Ctx Empty τ) (.snoc β X) c A) :
    AbortEquiv pe (Ctx.nil : Ctx Empty τ) β (.let₁ (.abort t) c)
      (.let₁ t (.let₁ (.abort (.bv 0)) c.underBinder)) A :=
  NativeProofs.commute_abort ht hc

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {A : τ} {a b : Expr Φ} {e : ε} {t s : Tm Empty Φ Γ.length}

/-- The discrete source equations at the original bound lower to the native
abort-extended relation with the bottom purity test. -/
theorem Eqv.toLetIter (h : Eqv Γ A e a b)
    (hl : a.toLetIter Γ.length = some t) (hr : b.toLetIter Γ.length = some s) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t s A :=
  NativeProofs.eqv_toLetIter h hl hr

/-- The two native endpoints retain the same effect bound as the source
equation. The purity parameter of the native equation is independently bottom. -/
theorem Eqv.toLetIter_at_bound (a b : TypedExpr Φ Γ A e) (h : Eqv Γ A e a.val b.val)
    (hl : a.val.toLetIter Γ.length = some t) (hr : b.val.toLetIter Γ.length = some s) :
    HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t A e ∧
    HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx s A e ∧
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t s A := by
  obtain ⟨_, ht, hta⟩ := a.prop.toLetIter
  obtain ⟨_, hs, hsb⟩ := b.prop.toLetIter
  exact ⟨Option.some.inj (ht.symm.trans hl) ▸ hta, Option.some.inj (hs.symm.trans hr) ▸ hsb,
    h.toLetIter hl hr⟩

/-- A typed source substitution from a bottom-annotated context lowers to a
pure native substitution. The existing native preservation theorem applies to
the entire derivation of the original equality. -/
theorem native_subst {Δ : EffectCtx τ ε} (hΓ : Γ.Pure)
    {σ : Nat → Expr Φ} {C : τ}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C)
    (hσ : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2) :
    ∃ t' s' : Tm Empty Φ Δ.length,
      (a.subst σ).toLetIter Δ.length = some t' ∧
      (b.subst σ).toLetIter Δ.length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Δ.toBoundCtx t' s' C :=
  NativeProofs.native_subst hΓ ht hs hn hσ

end Silmaril.Isotope.LetIter.PaperExpression.Source
