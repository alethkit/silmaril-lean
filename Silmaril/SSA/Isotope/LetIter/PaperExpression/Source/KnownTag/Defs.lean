module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Defs

/-! # Known sum tags of scoped source expressions -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]

/-- A scrutinee exposes a sum tag and a payload in the original context.
A pure unary let exposes its tag after capture-avoiding substitution. -/
inductive KnownTag (Γ : EffectCtx τ ε) (A B : τ) (e : ε) :
    Expr Φ → Sum (Expr Φ) (Expr Φ) → Prop where
  | inl {p : Expr Φ} : Wf Γ p A e → KnownTag Γ A B e (.inl p) (.inl p)
  | inr {p : Expr Φ} : Wf Γ p B e → KnownTag Γ A B e (.inr p) (.inr p)
  | letPure {X : τ} {a b : Expr Φ} {tag : Sum (Expr Φ) (Expr Φ)} :
      Wf Γ a X ⊥ → Wf ((X, ⊥) :: Γ) b (coprod A B) e →
      KnownTag Γ A B e (b.subst a.subst0) tag → KnownTag Γ A B e (.let₁ a b) tag

namespace KnownTag

variable (tag : Sum (Expr Φ) (Expr Φ))

/-- The injection certified by a known tag. -/
def injection : Expr Φ := tag.elim Expr.inl Expr.inr

/-- Execute the payload and continue with the selected case branch. -/
def residual (l r : Expr Φ) : Expr Φ := tag.elim (fun p => .let₁ p l) (fun p => .let₁ p r)

end KnownTag
end Silmaril.Isotope.LetIter.PaperExpression.Source
