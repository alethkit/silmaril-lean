module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Packing.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Reflection

/-! # Packing and reflection for the source SSA expression quotient -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A : τ} {e hi : ε}

/-- Equality of representatives is precisely the typed source relation at the same bound. -/
theorem ofExpr_eq_iff (a b : TypedExpr Φ Γ A e) :
    ofExpr a = ofExpr b ↔ Eqv Γ A e a.val b.val :=
  Quotient.eq

theorem unpack_pack (hp : Γ.Pure) (a : Class Φ Γ A e) :
    unpack hp (pack a) = a :=
  Proofs.unpack_pack_class hp a

theorem pack_unpack (hp : Γ.Pure) (a : Hom Φ (packType Γ) A e) :
    pack (Γ := Γ) (unpack hp a) = a :=
  Proofs.pack_unpack_class hp a

/-- Packing and reopening are inverse at each original effect bound. -/
def packing (hp : Γ.Pure) : Class Φ Γ A e ≃ Hom Φ (packType Γ) A e where
  toFun := pack
  invFun := unpack hp
  left_inv := unpack_pack hp
  right_inv := pack_unpack hp

/-- The interpreter agrees with the source packing substitution. -/
theorem denote_eq_pack (a : TypedExpr Φ Γ A e) :
    denote a = pack (ofExpr a) :=
  Proofs.denote_eq_pack a

/-- Equality of source denotations at the original effect bound is equivalent
to the discrete source expression equations in a pure context. -/
theorem denote_eq_iff_eqv (hp : Γ.Pure) (a b : TypedExpr Φ Γ A e) :
    denote a = denote b ↔ Eqv Γ A e a.val b.val :=
  Proofs.denote_eq_iff_eqv hp a b

/-- Reflection after effect weakening for all representatives of a pure
context is equivalent to injectivity on the packed source hom. -/
theorem reflection_after_weakening_iff (hp : Γ.Pure) (h : e ≤ hi) :
    (∀ a b : TypedExpr Φ Γ A e,
      weakenEffect h (denote a) = weakenEffect h (denote b) → Eqv Γ A e a.val b.val) ↔
      Function.Injective (weakenEffect (Γ := [(packType Γ, ⊥)]) (A := A) (Φ := Φ) h) :=
  Proofs.reflection_after_weakening_iff hp h

end Silmaril.Isotope.LetIter.PaperExpression.Source
