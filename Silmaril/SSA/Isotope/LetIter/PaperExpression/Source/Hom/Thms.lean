module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Hom.Defs

/-! # The packed source interpreter computes by typed hom operations -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A B D : τ} {e : ε}

theorem denote_var (i : Fin Γ.length) (hi : (Γ.get i).2 ≤ e) :
    denote (Φ := Φ) ⟨.var i.val, .var i hi⟩ = Hom.projection Γ i :=
  rfl

theorem denote_op {f : Φ} (hf : instrEff f ≤ e) (a : TypedExpr Φ Γ (instrSrc f) e) :
    denote ⟨.op f a.val, .op hf a.prop⟩ = Hom.applyInstruction hf (denote a) :=
  rfl

theorem denote_let1 (a : TypedExpr Φ Γ A e) (b : TypedExpr Φ ((A, ⊥) :: Γ) B e) :
    denote ⟨.let₁ a.val b.val, .let₁ a.prop b.prop⟩ = Hom.bind (denote a) (denote b) :=
  rfl

theorem denote_pair (a : TypedExpr Φ Γ A e) (b : TypedExpr Φ Γ B e) :
    denote ⟨.pair a.val b.val, .pair a.prop b.prop⟩ = Hom.pair (denote a) (denote b) :=
  rfl

theorem denote_unit :
    denote (Φ := Φ) ⟨.unit, .unit Γ e⟩ = Hom.toUnit :=
  rfl

theorem denote_let2 (a : TypedExpr Φ Γ (product A B) e)
    (b : TypedExpr Φ ((B, ⊥) :: (A, ⊥) :: Γ) D e) :
    denote ⟨.let₂ a.val b.val, .let₂ a.prop b.prop⟩ = Hom.bindPair (denote a) (denote b) :=
  rfl

theorem denote_inl (a : TypedExpr Φ Γ A e) :
    denote ⟨.inl a.val, Wf.inl (B := B) a.prop⟩ = Hom.inl (denote a) :=
  rfl

theorem denote_inr (b : TypedExpr Φ Γ B e) :
    denote ⟨.inr b.val, Wf.inr (A := A) b.prop⟩ = Hom.inr (denote b) :=
  rfl

theorem denote_case (a : TypedExpr Φ Γ (coprod A B) e)
    (l : TypedExpr Φ ((A, ⊥) :: Γ) D e) (r : TypedExpr Φ ((B, ⊥) :: Γ) D e) :
    denote ⟨.case a.val l.val r.val, .case a.prop l.prop r.prop⟩ =
      Hom.caseWithContext (denote a) (denote l) (denote r) :=
  rfl

theorem denote_abort (a : TypedExpr Φ Γ empty e) :
    denote ⟨.abort a.val, Wf.abort (A := A) a.prop⟩ = Hom.abort (denote a) :=
  rfl

end Silmaril.Isotope.LetIter.PaperExpression.Source
