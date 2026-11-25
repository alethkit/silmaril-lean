module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Path.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Native.Path

/-! # Eliminating known-tag excursions from a fixed-effect source path -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.RestrictedPath

open LocallyNameless (Tm AbortEquiv)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {A X Y : τ} {e : ε} {a b : PathTerm Φ Γ A e}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "β" => Γ.toBoundCtx

/-- Eliminate a restricted path's native excursions at the original effect bound. -/
theorem reflects (h : RestrictedPath e Γ A a b) (hp : Γ.Pure) :
    Eqv Γ A e a.source.val b.source.val :=
  PathProofs.reflects h hp

/-- Realize the native path, including its case excursions. -/
theorem toNative (h : RestrictedPath e Γ A a b) :
    AbortEquiv (⊥ : ε) Γ₀ β a.term b.term A :=
  PathProofs.toNative h

/-- Exhibit the entry, native branch step and `bindCase`, and exit of the left
excursion. The selected branch may itself take a restricted path. -/
theorem left_excursion (g : PathTerm Φ Γ (coprod X Y) e) (p : PathTerm Φ Γ X e)
    (tag : KnownTag Γ X Y e g.source.val (.inl p.source.val))
    {l l' : PathTerm Φ ((X, ⊥) :: Γ) A e} {r r' : Tm Empty Φ (Γ.length + 1)}
    (hl : RestrictedPath e ((X, ⊥) :: Γ) A l l')
    (hr : AbortEquiv (⊥ : ε) Γ₀ (.snoc β Y) r r' A) :
    AbortEquiv (⊥ : ε) Γ₀ β (p.let1 l).term (.case g.term l.term r) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.case g.term l.term r)
      (.let₁ g.term (.case (.bv 0) l'.term.underBinder r'.underBinder)) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ g.term (.case (.bv 0) l'.term.underBinder r'.underBinder))
      (p.let1 l').term A :=
  PathProofs.left_native g p tag hl.toNative hr

/-- Exhibit the corresponding native path when the right branch is selected. -/
theorem right_excursion (g : PathTerm Φ Γ (coprod X Y) e) (p : PathTerm Φ Γ Y e)
    (tag : KnownTag Γ X Y e g.source.val (.inr p.source.val))
    {l l' : Tm Empty Φ (Γ.length + 1)} {r r' : PathTerm Φ ((Y, ⊥) :: Γ) A e}
    (hl : AbortEquiv (⊥ : ε) Γ₀ (.snoc β X) l l' A)
    (hr : RestrictedPath e ((Y, ⊥) :: Γ) A r r') :
    AbortEquiv (⊥ : ε) Γ₀ β (p.let1 r).term (.case g.term l r.term) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.case g.term l r.term)
      (.let₁ g.term (.case (.bv 0) l'.underBinder r'.term.underBinder)) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ g.term (.case (.bv 0) l'.underBinder r'.term.underBinder))
      (p.let1 r').term A :=
  PathProofs.right_native g p tag hl hr.toNative

end Silmaril.Isotope.LetIter.PaperExpression.Source.RestrictedPath
