module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs

/-! # Fixed-effect source paths with native case excursions -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

open LocallyNameless (Tm CoreAxiom AbortSequence AbortEquiv)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]

/-- A typed source representative at a fixed bound and its native lowering. -/
structure PathTerm (Φ : Type v) [HasTy Φ τ] [HasEff Φ ε]
    (Γ : EffectCtx τ ε) (A : τ) (e : ε) where
  source : TypedExpr Φ Γ A e
  term : Tm Empty Φ Γ.length
  lowered : source.val.toLetIter Γ.length = some term

namespace PathTerm

variable {Γ : EffectCtx τ ε} {X A : τ} {e : ε}

/-- The source-representable boundary of a known-tag case excursion. -/
def let1 (p : PathTerm Φ Γ X e) (b : PathTerm Φ ((X, ⊥) :: Γ) A e) :
    PathTerm Φ Γ A e where
  source := ⟨.let₁ p.source.val b.source.val, .let₁ p.source.prop b.source.prop⟩
  term := .let₁ p.term b.term
  lowered := by
    have hb := b.lowered
    simp only [List.length_cons] at hb
    simp [Expr.toLetIter, p.lowered, hb]

end PathTerm

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- A finite path through source representatives. A known-tag excursion can
use arbitrary native equality in its discarded branch. Its selected branch
has a path of its own, and the outer boundaries are the two selected lets. -/
inductive RestrictedPath (e : ε) :
    (Γ : EffectCtx τ ε) → (A : τ) → PathTerm Φ Γ A e → PathTerm Φ Γ A e → Prop where
  | refl {Γ A} (a : PathTerm Φ Γ A e) : RestrictedPath e Γ A a a
  | source {Γ A} {a b : PathTerm Φ Γ A e} :
      Step Γ A e a.source.val b.source.val → RestrictedPath e Γ A a b
  | core {Γ A} {a b : PathTerm Φ Γ A e} :
      CoreAxiom (⊥ : ε) a.term b.term → RestrictedPath e Γ A a b
  | abortSequence {Γ A} {a b : PathTerm Φ Γ A e} :
      AbortSequence Γ₀ Γ.toBoundCtx a.term b.term A → RestrictedPath e Γ A a b
  | symm {Γ A} {a b : PathTerm Φ Γ A e} :
      RestrictedPath e Γ A a b → RestrictedPath e Γ A b a
  | trans {Γ A} {a b c : PathTerm Φ Γ A e} :
      RestrictedPath e Γ A a b → RestrictedPath e Γ A b c → RestrictedPath e Γ A a c
  | left {Γ : EffectCtx τ ε} {X Y A} {l l' : PathTerm Φ ((X, ⊥) :: Γ) A e} {r r' : Tm Empty Φ (Γ.length + 1)}
      (guard : PathTerm Φ Γ (coprod X Y) e) (payload : PathTerm Φ Γ X e) :
      KnownTag Γ X Y e guard.source.val (.inl payload.source.val) →
      RestrictedPath e ((X, ⊥) :: Γ) A l l' →
      AbortEquiv (⊥ : ε) Γ₀ (.snoc Γ.toBoundCtx Y) r r' A →
      RestrictedPath e Γ A (payload.let1 l) (payload.let1 l')
  | right {Γ : EffectCtx τ ε} {X Y A} {l l' : Tm Empty Φ (Γ.length + 1)} {r r' : PathTerm Φ ((Y, ⊥) :: Γ) A e}
      (guard : PathTerm Φ Γ (coprod X Y) e) (payload : PathTerm Φ Γ Y e) :
      KnownTag Γ X Y e guard.source.val (.inr payload.source.val) →
      AbortEquiv (⊥ : ε) Γ₀ (.snoc Γ.toBoundCtx X) l l' A →
      RestrictedPath e ((Y, ⊥) :: Γ) A r r' →
      RestrictedPath e Γ A (payload.let1 r) (payload.let1 r')

end Silmaril.Isotope.LetIter.PaperExpression.Source
