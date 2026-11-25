module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Packing

/-! # Typed operations on the fixed-effect source homs -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Hom

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {X A B D : τ} {e : ε}

theorem substInput_wf (input : TypedExpr Φ Γ X ⊥) (body : TypedExpr Φ [(X, ⊥)] A e) :
    Wf Γ (body.val.subst input.val.subst0) A e :=
  Proofs.wf_subst body.prop (Proofs.oneSubst input.prop)

theorem substInput_eqv (input : TypedExpr Φ Γ X ⊥) {a b : Expr Φ}
    (h : Eqv [(X, ⊥)] A e a b) : Eqv Γ A e (a.subst input.val.subst0) (b.subst input.val.subst0) :=
  Proofs.eqv_subst h (Proofs.oneSubst input.prop)

theorem projection_wf (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    Wf [(packType Γ, ⊥)] (project i.val (.var 0 : Expr Φ)) (Γ.get i).1 e :=
  Proofs.project_wf Γ i (.var 0 bot_le)

@[expose] section

/-- Reindex a hom along a pure expression supplying its input. -/
def substInput (input : TypedExpr Φ Γ X ⊥) (body : Hom Φ X A e) : Class Φ Γ A e :=
  Quotient.map (fun t => ⟨t.val.subst input.val.subst0, substInput_wf input t⟩)
    (fun _ _ h => substInput_eqv input h) body

/-- Project an original slot out of the product environment. -/
def projection (Γ : EffectCtx τ ε) (i : Fin Γ.length) : Hom Φ (packType Γ) (Γ.get i).1 e :=
  ofExpr ⟨project i.val (.var 0), projection_wf Γ i⟩

/-- Run the instruction after its argument, within the common effect bound. -/
def applyInstruction {f : Φ} (hf : instrEff f ≤ e) (a : Hom Φ X (instrSrc f) e) :
    Hom Φ X (instrTrg f) e :=
  Quotient.map (fun t => ⟨.op f t.val, .op hf t.prop⟩)
    (fun _ _ h => Eqv.op hf h) a

/-- The pure unit expression from any input. -/
def toUnit : Hom Φ X unit e := ofExpr ⟨.unit, .unit _ _⟩

/-- Pair the two computations in left-to-right order. -/
def pair (a : Hom Φ X A e) (b : Hom Φ X B e) : Hom Φ X (product A B) e :=
  Quotient.map₂ (fun t s => ⟨.pair t.val s.val, .pair t.prop s.prop⟩)
    (fun _ _ h₁ _ _ h₂ => Eqv.pair h₁ h₂) a b

/-- Retain the input and append the new bound value. -/
def extendedInput (X A : τ) : TypedExpr Φ ([(A, ⊥), (X, ⊥)] : EffectCtx τ ε) (product X A) ⊥ :=
  ⟨.pair (.var 1) (.var 0), .pair (.var 1 le_rfl) (.var 0 le_rfl)⟩

/-- Retain the input and append the two bound values in product order. -/
def extendedPairInput (X A B : τ) :
    TypedExpr Φ ([(B, ⊥), (A, ⊥), (X, ⊥)] : EffectCtx τ ε) (product (product X A) B) ⊥ :=
  ⟨.pair (.pair (.var 2) (.var 1)) (.var 0),
    .pair (.pair (.var 2 le_rfl) (.var 1 le_rfl)) (.var 0 le_rfl)⟩

/-- Run the initializer and use the retained input and its value in the body. -/
def bind (a : Hom Φ X A e) (b : Hom Φ (product X A) B e) : Hom Φ X B e :=
  Quotient.map₂ (fun t s => ⟨.let₁ t.val s.val, .let₁ t.prop s.prop⟩)
    (fun _ _ h₁ _ _ h₂ => Eqv.let1 h₁ h₂) a (substInput (extendedInput X A) b)

/-- Run the initializer and append its two product components to the context. -/
def bindPair (a : Hom Φ X (product A B) e) (b : Hom Φ (product (product X A) B) D e) :
    Hom Φ X D e :=
  Quotient.map₂ (fun t s => ⟨.let₂ t.val s.val, .let₂ t.prop s.prop⟩)
    (fun _ _ h₁ _ _ h₂ => Eqv.let2 h₁ h₂) a (substInput (extendedPairInput X A B) b)

def inl (a : Hom Φ X A e) : Hom Φ X (coprod A B) e :=
  Quotient.map (fun t => ⟨.inl t.val, .inl t.prop⟩) (fun _ _ h => Eqv.inl h) a

def inr (b : Hom Φ X B e) : Hom Φ X (coprod A B) e :=
  Quotient.map (fun t => ⟨.inr t.val, .inr t.prop⟩) (fun _ _ h => Eqv.inr h) b

/-- Evaluate the discriminant and retain the input in the selected branch. -/
def caseWithContext (a : Hom Φ X (coprod A B) e)
    (l : Hom Φ (product X A) D e) (r : Hom Φ (product X B) D e) : Hom Φ X D e :=
  let runCase (t : TypedExpr Φ [(X, ⊥)] (coprod A B) e)
      (left : Class Φ [(A, ⊥), (X, ⊥)] D e) (right : Class Φ [(B, ⊥), (X, ⊥)] D e) :
      Hom Φ X D e :=
    Quotient.map₂ (fun u v => ⟨.case t.val u.val v.val, .case t.prop u.prop v.prop⟩)
      (fun _ _ hl _ _ hr => Eqv.case (.refl t.prop) hl hr) left right
  let left := substInput (extendedInput X A) l
  let right := substInput (extendedInput X B) r
  Quotient.liftOn a (fun t => runCase t left right)
    (fun t s h => Quotient.inductionOn₂ left right
      (motive := fun u v => runCase t u v = runCase s u v) fun u v =>
        Quotient.sound (Eqv.case h (.refl u.prop) (.refl v.prop)))

def abort (a : Hom Φ X empty e) : Hom Φ X A e :=
  Quotient.map (fun t => ⟨.abort t.val, .abort t.prop⟩) (fun _ _ h => Eqv.abort h) a

end

end Silmaril.Isotope.LetIter.PaperExpression.Source.Hom
