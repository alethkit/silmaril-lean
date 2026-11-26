module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Observation.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Defs

/-! # Written continuation pairs with shared visible requests -/

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

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyReflection
