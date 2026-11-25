module

public import Silmaril.SSA.Isotope.LetIter.Effects.Thms

/-! # The written SSA expression grammar and exact typing

The raw expression grammar and the discrete-type specialization of well-formedness
follow the public BSD-0 source `imbrem/debruijn-ssa` at
`316bd9a6511d165b5d1d0042956a72e0f5547091`,
`DeBruijnSSA/BinSyntax/Syntax/Definitions.lean` and
`DeBruijnSSA/BinSyntax/Typing/Term/Basic.lean`.
The ambient type carriers and primitive signature use Silmaril's type formers,
instruction endpoints and instruction effects.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression

open LocallyNameless (Tm)

/-- The SSA expression grammar with unbounded de Bruijn indices. -/
inductive Expr (Φ : Type v) where
  | var : Nat → Expr Φ
  | op : Φ → Expr Φ → Expr Φ
  | let₁ : Expr Φ → Expr Φ → Expr Φ
  | pair : Expr Φ → Expr Φ → Expr Φ
  | unit : Expr Φ
  | let₂ : Expr Φ → Expr Φ → Expr Φ
  | inl : Expr Φ → Expr Φ
  | inr : Expr Φ → Expr Φ
  | case : Expr Φ → Expr Φ → Expr Φ → Expr Φ
  | abort : Expr Φ → Expr Φ

variable {τ : Type u} {Φ : Type v} {ε : Type w}

abbrev EffectCtx (τ : Type u) (ε : Type w) := List (τ × ε)

/-- Erase the slot effects while preserving newest-first type lookup. -/
def EffectCtx.toBoundCtx : (Γ : EffectCtx τ ε) → BoundCtx τ Γ.length
  | [] => .nil
  | (A, _) :: Γ => .snoc (toBoundCtx Γ) A

/-- Every context slot has bottom effect. -/
def EffectCtx.Pure [Bot ε] (Γ : EffectCtx τ ε) : Prop :=
  ∀ i : Fin Γ.length, (Γ.get i).2 = ⊥

/-- Resolve the indices at the ambient scope, extending it under each binder. -/
def Expr.toLetIter (n : Nat) : Expr Φ → Option (Tm Empty Φ n)
  | .var i => if h : i < n then some (.bv ⟨i, h⟩) else none
  | .op f a => (a.toLetIter n).map (.op f)
  | .let₁ a b => (a.toLetIter n).bind fun t => (b.toLetIter (n + 1)).map (.let₁ t)
  | .pair a b => (a.toLetIter n).bind fun t => (b.toLetIter n).map (.pair t)
  | .unit => some .unit
  | .let₂ a b => (a.toLetIter n).bind fun t => (b.toLetIter (n + 2)).map (.let₂ t)
  | .inl a => (a.toLetIter n).map .inl
  | .inr a => (a.toLetIter n).map .inr
  | .case a l r => (a.toLetIter n).bind fun t =>
      (l.toLetIter (n + 1)).bind fun s => (r.toLetIter (n + 1)).map (.case t s)
  | .abort a => (a.toLetIter n).map .abort

section Typing

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [Bot ε]

/-- The source expression typing rules with invariant types and effect upper bounds.
The context is newest-first, and binders introduce bottom-annotated slots. -/
inductive Wf : EffectCtx τ ε → Expr Φ → τ → ε → Prop where
  | var {Γ : EffectCtx τ ε} (i : Fin Γ.length) {e : ε} (hi : (Γ.get i).2 ≤ e) :
      Wf Γ (.var i.val) (Γ.get i).1 e
  | op {Γ : EffectCtx τ ε} {f : Φ} {a : Expr Φ} {e : ε}
      (hf : instrEff f ≤ e) (ha : Wf Γ a (instrSrc f) e) :
      Wf Γ (.op f a) (instrTrg f) e
  | let₁ {Γ : EffectCtx τ ε} {a b : Expr Φ} {A B : τ} {e : ε}
      (ha : Wf Γ a A e) (hb : Wf ((A, ⊥) :: Γ) b B e) : Wf Γ (.let₁ a b) B e
  | pair {Γ : EffectCtx τ ε} {a b : Expr Φ} {A B : τ} {e : ε}
      (ha : Wf Γ a A e) (hb : Wf Γ b B e) : Wf Γ (.pair a b) (product A B) e
  | unit (Γ : EffectCtx τ ε) (e : ε) : Wf Γ (.unit : Expr Φ) Silmaril.unit e
  | let₂ {Γ : EffectCtx τ ε} {a b : Expr Φ} {A B C : τ} {e : ε}
      (ha : Wf Γ a (product A B) e) (hb : Wf ((B, ⊥) :: (A, ⊥) :: Γ) b C e) :
      Wf Γ (.let₂ a b) C e
  | inl {Γ : EffectCtx τ ε} {a : Expr Φ} {A B : τ} {e : ε}
      (ha : Wf Γ a A e) : Wf Γ (.inl a) (coprod A B) e
  | inr {Γ : EffectCtx τ ε} {b : Expr Φ} {A B : τ} {e : ε}
      (hb : Wf Γ b B e) : Wf Γ (.inr b) (coprod A B) e
  | case {Γ : EffectCtx τ ε} {a l r : Expr Φ} {A B C : τ} {e : ε}
      (ha : Wf Γ a (coprod A B) e) (hl : Wf ((A, ⊥) :: Γ) l C e)
      (hr : Wf ((B, ⊥) :: Γ) r C e) : Wf Γ (.case a l r) C e
  | abort {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε}
      (ha : Wf Γ a empty e) : Wf Γ (.abort a) A e

end Typing

end Silmaril.Isotope.LetIter.PaperExpression
