module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Native.Reflection

/-! # Reflection of native generators on their fixed-effect source image -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

open LocallyNameless (Tm CoreAxiom AbortSequence)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {Γ : EffectCtx τ ε} {A : τ} {e : ε}

/-- Source abort sequencing is derived from the source commuting conversion
and let eta. The payload may have effects at the given bound. -/
theorem Eqv.abortSequence [Preorder ε] [OrderBot ε] {a : Expr Φ} (ha : Wf Γ a empty e) :
    Eqv Γ A e (.abort a) (.let₁ a (.abort (.var 0))) :=
  NativeProofs.source_abortSequence ha

/-- Both orientations of the native abort-sequencing generator reflect
between source representatives at the same effect bound. -/
theorem eqv_of_abortSequence_toLetIter [Preorder ε] [OrderBot ε]
    {t s : Tm Empty Φ Γ.length} (a b : TypedExpr Φ Γ A e)
    (ha : a.val.toLetIter Γ.length = some t) (hb : b.val.toLetIter Γ.length = some s)
    (h : AbortSequence (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx t s A) :
    Eqv Γ A e a.val b.val :=
  NativeProofs.abortSequence_reflection a b ha hb h

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {t s : Tm Empty Φ Γ.length}

/-- An exact native axiom instance between two lowered expressions in a
pure source context reflects at their original effect bound. -/
theorem eqv_of_coreAxiom_toLetIter (hp : Γ.Pure) (a b : TypedExpr Φ Γ A e)
    (ha : a.val.toLetIter Γ.length = some t) (hb : b.val.toLetIter Γ.length = some s)
    (h : CoreAxiom (⊥ : ε) t s) :
    Eqv Γ A e a.val b.val :=
  NativeProofs.core_reflection hp a b ha hb h

end Silmaril.Isotope.LetIter.PaperExpression.Source
