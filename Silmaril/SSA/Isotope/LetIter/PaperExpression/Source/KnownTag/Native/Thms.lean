module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Native

/-! # Known-tag normalization through a native discarded branch -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTag

open LocallyNameless (Tm HasType HasTypeEffect AbortEquiv)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {A B C : τ} {e : ε} {s p : Expr Φ}
  {ts tp : Tm Empty Φ Γ.length} {l r : Tm Empty Φ (Γ.length + 1)}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "β" => Γ.toBoundCtx

/-- A known left tag bypasses the native right branch in direct and let-bound cases.
The discarded branch carries exact typing alone. -/
theorem native_inl (h : KnownTag Γ A B e s (.inl p))
    (hs : s.toLetIter Γ.length = some ts) (hp : p.toLetIter Γ.length = some tp)
    (hl : HasTypeEffect Γ₀ (.snoc β A) l C e) (hr : HasType Φ Γ₀ (.snoc β B) r C) :
    HasTypeEffect Γ₀ β (.let₁ tp l) C e ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.case ts l r) (.let₁ tp l) C ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ ts (.case (.bv 0) l.underBinder r.underBinder)) (.let₁ tp l) C :=
  KnownTagProofs.native_inl h hs hp hl hr

/-- A known right tag bypasses the native left branch in direct and let-bound cases.
The selected residual retains the original effect bound. -/
theorem native_inr (h : KnownTag Γ A B e s (.inr p))
    (hs : s.toLetIter Γ.length = some ts) (hp : p.toLetIter Γ.length = some tp)
    (hl : HasType Φ Γ₀ (.snoc β A) l C) (hr : HasTypeEffect Γ₀ (.snoc β B) r C e) :
    HasTypeEffect Γ₀ β (.let₁ tp r) C e ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.case ts l r) (.let₁ tp r) C ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ ts (.case (.bv 0) l.underBinder r.underBinder)) (.let₁ tp r) C :=
  KnownTagProofs.native_inr h hs hp hl hr

end Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTag
