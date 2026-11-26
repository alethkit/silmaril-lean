module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover

/-! # Original-bound source normalization across constructor covers -/

public section

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w}
  {Γ : EffectCtx (Ty α) ε} {a : Expr Φ}

/-- Constructor syntax is closed under substitution by constructor values. -/
theorem Value.subst (h : Value a) {σ : Nat → Expr Φ} (hs : ∀ i, Value (σ i)) :
    Value (a.subst σ) :=
  Proofs.Value.subst h hs

section Existence

variable [Preorder ε] [OrderBot ε]

/-- Every pure finite context admits a cover, including nullary slots. -/
theorem exists_cover (hΓ : Γ.Pure) : Nonempty (ConstructorCover Γ) :=
  Proofs.exists_cover hΓ

end Existence

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {A : Ty α} {e : ε}

/-- Normalize the atomic leaves with any typed original-bound normalizer and
rebuild the result in the original context. -/
theorem eqv_render (cover : ConstructorCover Γ) (ha : Wf Γ a A e)
    {leaf : EffectCtx (Ty α) ε → Expr Φ → Expr Φ}
    (h : cover.AllLeaves (fun Δ x => Wf Δ x A e → Eqv Δ A e x (leaf Δ x)) a) :
    Eqv Γ A e a (cover.render leaf a) :=
  Proofs.eqv_render cover ha h

/-- The unchanged specializations of an expression reassemble to an
equivalent expression at its original effect bound. -/
theorem eqv_rebuild (cover : ConstructorCover Γ) (ha : Wf Γ a A e) :
    Eqv Γ A e a (cover.render (fun _ x => x) a) :=
  Proofs.eqv_rebuild cover ha

/-- A primitive applied to a constructor value retains the original symbol
and type at each atomic leaf. Each specialized argument is typed at bottom. -/
theorem primitive_leaves (cover : ConstructorCover Γ) (hΓ : Γ.Pure) (f : Φ)
    (ha : Wf Γ a (instrSrc f) e) (hv : Value a) :
    cover.AllLeaves
      (fun Δ request => ∃ v, request = .op f v ∧ Value v ∧ Wf Δ v (instrSrc f) ⊥)
      (.op f a) :=
  Proofs.primitive_leaves cover hΓ f ha hv

/-- Evaluate an arbitrary primitive argument exactly once. Every reachable
input leaf sends that primitive one fully typed constructor argument.
The reply is bound once and the continuation specializes its slots through
a second constructor cover, including the empty-response branch. -/
theorem factor_primitive (hΓ : Γ.Pure) {f : Φ} (hf : instrEff f ≤ e)
    {arg k : Expr Φ} (ha : Wf Γ arg (instrSrc f) e)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) :
    ∃ input : ConstructorCover ((instrSrc f, ⊥) :: Γ),
    ∃ reply : ConstructorCover ((instrTrg f, ⊥) :: Γ),
      input.AllLeaves
        (fun Δ request => ∃ v, request = .op f v ∧ Value v ∧ Wf Δ v (instrSrc f) ⊥)
        (.op f (.var 0)) ∧
      Eqv Γ A e (.let₁ (.op f arg) k)
        (.let₁ (.let₁ arg (input.render (fun _ x => x) (.op f (.var 0))))
          (reply.render (fun _ x => x) k)) :=
  Proofs.factor_primitive hΓ hf ha hk

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover
