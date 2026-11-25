module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag

/-! # Source case normalization after detecting a sum tag -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTag

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A B C X : τ} {e : ε}
  {s s' p l r : Expr Φ} {tag tag' : Sum (Expr Φ) (Expr Φ)}

/-- The selected payload is in the original context at the original effect bound. -/
theorem payload_wf (h : KnownTag Γ A B e s tag) :
    tag.elim (fun p => Wf Γ p A e) (fun p => Wf Γ p B e) :=
  KnownTagProofs.payload_wf h

/-- Substituting a typed pure initializer preserves the known tag and
substitutes it into the selected payload without capturing a binder. -/
theorem subst0 (h : KnownTag ((X, ⊥) :: Γ) A B e s tag) (hp : Wf Γ p X ⊥) :
    KnownTag Γ A B e (s.subst p.subst0) (tag.map (Expr.subst p.subst0) (Expr.subst p.subst0)) :=
  KnownTagProofs.subst0 h hp

theorem unique (h : KnownTag Γ A B e s tag) (h' : KnownTag Γ A B e s tag') : tag = tag' :=
  KnownTagProofs.unique h h'

/-- The scoped normalization uses source beta at the original bound. -/
theorem eqv_injection (h : KnownTag Γ A B e s tag) :
    Eqv Γ (coprod A B) e s (injection tag) :=
  KnownTagProofs.eqv_injection h

theorem case_eqv (h : KnownTag Γ A B e s tag)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.case s l r) (residual tag l r) :=
  KnownTagProofs.case_eqv h hl hr

/-- The same residual works with the let-bound scrutinee of source `case_bind`. -/
theorem bindCase_eqv (h : KnownTag Γ A B e s tag)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.let₁ s (.case (.var 0) l.wk1 r.wk1)) (residual tag l r) :=
  KnownTagProofs.bindCase_eqv h hl hr

/-- A supplied source equation between guards relates their selected residuals. -/
theorem residual_eqv (h : KnownTag Γ A B e s tag) (h' : KnownTag Γ A B e s' tag')
    (heq : Eqv Γ (coprod A B) e s s')
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (residual tag l r) (residual tag' l r) :=
  KnownTagProofs.residual_eqv h h' heq hl hr

end Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTag
