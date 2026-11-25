module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Packing.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Packing

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A : τ} {e hi : ε}

theorem denote_eq_pack (a : TypedExpr Φ Γ A e) : denote a = pack (ofExpr a) :=
  Quotient.sound (denote_eqv_pack a.prop)

theorem unpack_pack_class (hp : Γ.Pure) (a : Class Φ Γ A e) : unpack hp (pack a) = a :=
  Quotient.inductionOn a fun t => Quotient.sound (unpack_pack hp t.prop)

theorem pack_unpack_class (hp : Γ.Pure) (a : Hom Φ (packType Γ) A e) : pack (unpack hp a) = a :=
  Quotient.inductionOn a fun t => Quotient.sound (pack_unpack (Γ := Γ) t.prop)

private theorem denote_surjective (hp : Γ.Pure) :
    Function.Surjective (denote (Φ := Φ) (Γ := Γ) (A := A) (e := e)) := by
  intro f
  have representative (q : Class Φ Γ A e) : ∃ a : TypedExpr Φ Γ A e, ofExpr a = q :=
    Quotient.inductionOn q fun a => ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := representative (unpack hp f)
  exact ⟨a, (denote_eq_pack a).trans ((congrArg pack ha).trans (pack_unpack_class hp f))⟩

theorem denote_eq_iff_eqv (hp : Γ.Pure) (a b : TypedExpr Φ Γ A e) :
    denote a = denote b ↔ Eqv Γ A e a.val b.val := by
  rw [denote_eq_pack, denote_eq_pack]
  constructor
  · intro h
    exact Quotient.exact ((unpack_pack_class hp (ofExpr a)).symm.trans
      ((congrArg (unpack hp) h).trans (unpack_pack_class hp (ofExpr b))))
  · intro h
    exact congrArg pack (Quotient.sound h)

theorem reflection_after_weakening_iff (hp : Γ.Pure) (h : e ≤ hi) :
    (∀ a b : TypedExpr Φ Γ A e,
      weakenEffect h (denote a) = weakenEffect h (denote b) → Eqv Γ A e a.val b.val) ↔
      Function.Injective (weakenEffect (Γ := [(packType Γ, ⊥)]) (A := A) (Φ := Φ) h) := by
  constructor
  · intro reflect f g equal
    obtain ⟨a, ha⟩ := denote_surjective (Φ := Φ) (A := A) (e := e) hp f
    obtain ⟨b, hb⟩ := denote_surjective (Φ := Φ) (A := A) (e := e) hp g
    have hw : weakenEffect h (denote a) = weakenEffect h (denote b) := by
      rw [ha, hb]
      exact equal
    exact ha.symm.trans (((denote_eq_iff_eqv hp a b).mpr (reflect a b hw)).trans hb)
  · intro injective a b equal
    exact (denote_eq_iff_eqv hp a b).mp (injective equal)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs
