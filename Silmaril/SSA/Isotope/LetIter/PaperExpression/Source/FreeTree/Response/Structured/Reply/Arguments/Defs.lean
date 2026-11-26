module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Defs

/-! # Finite written call arguments and their sequenced forms -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (ConstructorLeaf)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]

/-- A typed fragment with bottom-typed constructor expressions, visible
calls with recursively computed arguments, unary lets, and ordered pairs. Intermediate
types and visible replies may be structured. -/
inductive Raw (e : ε) : EffectCtx (Ty α) ε → Ty α → Expr Φ → Prop
  | leaf {Γ : EffectCtx (Ty α) ε} {A : Ty α} {a : Expr Φ}
      (typed : Wf Γ a A ⊥) (leaf : ConstructorLeaf a) : Raw e Γ A a
  | call {Γ : EffectCtx (Ty α) ε} {f : Φ} {arg : Expr Φ}
      (visible : ¬ IsPure (⊥ : ε) f) (bound : instrEff f ≤ e)
      (argument : Raw e Γ (instrSrc f) arg) : Raw e Γ (instrTrg f) (.op f arg)
  | let1 {Γ : EffectCtx (Ty α) ε} {A B : Ty α} {a k : Expr Φ}
      (init : Raw e Γ A a) (body : Raw e ((A, ⊥) :: Γ) B k) : Raw e Γ B (.let₁ a k)
  | pair {Γ : EffectCtx (Ty α) ε} {A B : Ty α} {a b : Expr Φ}
      (left : Raw e Γ A a) (right : Raw e Γ B b) : Raw e Γ (.product A B) (.pair a b)

/-- A finite branching expression. A straight-line prefix computes a sum
scrutinee, then only the selected arm runs. The arms may themselves branch.
A straight-line initializer can also introduce a value before a branching body. -/
inductive CaseRaw (e : ε) : EffectCtx (Ty α) ε → Ty α → Expr Φ → Prop
  | straight {Γ : EffectCtx (Ty α) ε} {A : Ty α} {a : Expr Φ}
      (body : Raw e Γ A a) : CaseRaw e Γ A a
  | let1 {Γ : EffectCtx (Ty α) ε} {A B : Ty α} {a k : Expr Φ}
      (init : Raw e Γ A a) (body : CaseRaw e ((A, ⊥) :: Γ) B k) : CaseRaw e Γ B (.let₁ a k)
  | case {Γ : EffectCtx (Ty α) ε} {A B C : Ty α} {s l r : Expr Φ}
      (scrutinee : Raw e Γ (.coprod A B) s)
      (left : CaseRaw e ((A, ⊥) :: Γ) C l) (right : CaseRaw e ((B, ⊥) :: Γ) C r) :
      CaseRaw e Γ C (.case s l r)

/-- A sequence of visible requests with bottom-typed constructor arguments,
ending in a bottom-typed constructor value. Continuations can use their
whole reply as a single variable. -/
inductive Sequenced (e : ε) : EffectCtx (Ty α) ε → Ty α → Expr Φ → Prop
  | leaf {Γ : EffectCtx (Ty α) ε} {A : Ty α} {a : Expr Φ}
      (typed : Wf Γ a A ⊥) (leaf : ConstructorLeaf a) : Sequenced e Γ A a
  | call {Γ : EffectCtx (Ty α) ε} {A : Ty α} {f : Φ} {arg k : Expr Φ}
      (visible : ¬ IsPure (⊥ : ε) f) (bound : instrEff f ≤ e)
      (typed : Wf Γ arg (instrSrc f) ⊥) (leaf : ConstructorLeaf arg)
      (body : Sequenced e ((instrTrg f, ⊥) :: Γ) A k) :
      Sequenced e Γ A (.let₁ (.op f arg) k)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
