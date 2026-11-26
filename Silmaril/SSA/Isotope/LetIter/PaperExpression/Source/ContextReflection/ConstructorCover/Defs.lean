module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Defs

/-! # Constructor covers of source contexts -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w}

/-- A finite decomposition of bottom-annotated slots into atomic contexts.
An empty slot closes the branch. A product introduces both fields and a sum
introduces a payload slot in each of two branches. -/
inductive ConstructorCover [Bot ε] : EffectCtx (Ty α) ε → Type (max u w)
  | atomic {Γ} (atoms : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = .base x) :
      ConstructorCover Γ
  | empty {Γ} (i : Fin Γ.length) (ty : (Γ.get i).1 = .empty) (eff : (Γ.get i).2 = ⊥) :
      ConstructorCover Γ
  | unit {Γ} (i : Fin Γ.length) (ty : (Γ.get i).1 = .unit) (eff : (Γ.get i).2 = ⊥)
      (next : ConstructorCover (UnitSlot.eraseCtx Γ i)) : ConstructorCover Γ
  | product {Γ A B} (i : Fin Γ.length) (ty : (Γ.get i).1 = .product A B) (eff : (Γ.get i).2 = ⊥)
      (next : ConstructorCover (ProductSplit.splitCtx Γ i A B)) : ConstructorCover Γ
  | sum {Γ A B} (i : Fin Γ.length) (ty : (Γ.get i).1 = .coprod A B) (eff : (Γ.get i).2 = ⊥)
      (left : ConstructorCover (SumSplit.branchCtx Γ i A))
      (right : ConstructorCover (SumSplit.branchCtx Γ i B)) : ConstructorCover Γ

namespace ConstructorCover

variable [Bot ε]

/-- Specialize an expression through the cover, transform its atomic leaves,
and reassemble it using the original slot eliminators. -/
def render (leaf : EffectCtx (Ty α) ε → Expr Φ → Expr Φ) :
    {Γ : EffectCtx (Ty α) ε} → ConstructorCover Γ → Expr Φ → Expr Φ
  | Γ, .atomic _, a => leaf Γ a
  | _, .empty i _ _, _ => .abort (.var i)
  | _, .unit i _ _ next, a => (next.render leaf (UnitSlot.specializeUnit i a)).wk (UnitSlot.insertIndex i)
  | _, .product i _ _ next, a =>
      .let₂ (.var i) ((next.render leaf (ProductSplit.split i a)).wk (Expr.liftWk (SumSplit.toFront i)))
  | _, .sum i _ _ l r, a => SumSplit.caseArms i (l.render leaf (SumSplit.left i a))
      (r.render leaf (SumSplit.right i a))

/-- The predicate tests raw specializations before reconstruction. Empty
branches contribute no atomic leaf. -/
def AllLeaves (P : EffectCtx (Ty α) ε → Expr Φ → Prop) :
    {Γ : EffectCtx (Ty α) ε} → ConstructorCover Γ → Expr Φ → Prop
  | Γ, .atomic _, a => P Γ a
  | _, .empty .., _ => True
  | _, .unit i _ _ next, a => next.AllLeaves P (UnitSlot.specializeUnit i a)
  | _, .product i _ _ next, a => next.AllLeaves P (ProductSplit.split i a)
  | _, .sum i _ _ l r, a => l.AllLeaves P (SumSplit.left i a) ∧ r.AllLeaves P (SumSplit.right i a)

/-- Constructor syntax over open variables. Typing in an atomic context then
makes every variable leaf atomic without restricting the enclosing type. -/
inductive Value : Expr Φ → Prop
  | var (i : Nat) : Value (.var i)
  | unit : Value .unit
  | pair {a b} : Value a → Value b → Value (.pair a b)
  | inl {a} : Value a → Value (.inl a)
  | inr {a} : Value a → Value (.inr a)

end ConstructorCover
end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection
