module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Observation.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Defs

/-! # Finite written programs and comparison trees with recursive replies -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (ConstructorLeaf)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]

/-- A finite comparison tree for written endpoints. It tests both pure leaves,
or one common visible request followed by a recursive comparison for every
constructor reply. The raw continuations can retain the entire reply.
A source equation can expose the next constructor when needed. -/
inductive Shared (A : Ty α) (e : ε) : EffectCtx (Ty α) ε → Expr Φ → Expr Φ → Prop
  | leaf {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ}
      (ha : Wf Γ a A ⊥) (hb : Wf Γ b A ⊥)
      (la : ConstructorLeaf a) (lb : ConstructorLeaf b) : Shared A e Γ a b
  | call {Γ : EffectCtx (Ty α) ε} {f : Φ} {arg k l : Expr Φ}
      (visible : ¬ IsPure (⊥ : ε) f) (bound : instrEff f ≤ e)
      (typed : Wf Γ arg (instrSrc f) ⊥) (leaf : ConstructorLeaf arg)
      (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (hl : Wf ((instrTrg f, ⊥) :: Γ) l A e)
      (children : ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts (instrTrg f)),
        Shared A e (ReplyShape.fieldCtx sorts Γ) (shape.specialize Γ k) (shape.specialize Γ l)) :
      Shared A e Γ (.let₁ (.op f arg) k) (.let₁ (.op f arg) l)
  | normalize {Γ : EffectCtx (Ty α) ε} {a b a' b' : Expr Φ}
      (ha : Eqv Γ A e a a') (hb : Eqv Γ A e b b') (next : Shared A e Γ a' b') :
      Shared A e Γ a b

/-- Recognize a written endpoint independently of any expression it may
be compared with. Each node records its own source equation to the exposed
leaf or call at the original bound. The children are the raw continuations
after reply-shape substitution. -/
inductive Written (A : Ty α) (e : ε) : EffectCtx (Ty α) ε → Expr Φ → Prop
  | leaf {Γ : EffectCtx (Ty α) ε} {a value : Expr Φ}
      (head : Eqv Γ A e a value) (typed : Wf Γ value A ⊥) (leaf : ConstructorLeaf value) :
      Written A e Γ a
  | call {Γ : EffectCtx (Ty α) ε} {a arg k : Expr Φ} {f : Φ}
      (head : Eqv Γ A e a (.let₁ (.op f arg) k))
      (visible : ¬ IsPure (⊥ : ε) f) (bound : instrEff f ≤ e)
      (typed : Wf Γ arg (instrSrc f) ⊥) (leaf : ConstructorLeaf arg)
      (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e)
      (children : ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts (instrTrg f)),
        Written A e (ReplyShape.fieldCtx sorts Γ) (shape.specialize Γ k)) :
      Written A e Γ a

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection
