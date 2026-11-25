module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Thms

/-! # The native representative map on fixed-effect source homs -/

@[expose] public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

/-- A singleton source context packs its input with the unit. -/
def singletonInput (M : TypeModel τ V) (X : τ) : M.obj X ⟶ M.obj (product unit X) :=
  (λ_ (M.obj X)).inv ≫ (M.unitIso.inv ▷ M.obj X) ≫ (M.productIso unit X).inv

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) (M : TypeModel τ V) [DistributiveFreydCategory J] [HasTy Φ τ] [InstructionModel J M Φ]
  [HasEff Φ ε] [Preorder ε] [OrderBot ε]

/-- Exact evidence needed to descend native representative evaluation to
the source hom quotient at e. The reflexive case includes independence
of the choice of exact native typing derivation. -/
def RespectsSourceEqv (e : ε) : Prop :=
  ∀ {X A : τ} (a b : TypedExpr Φ [(X, ⊥)] A e), Eqv [(X, ⊥)] A e a.val b.val →
    ∀ (da : Lowering [(X, (⊥ : ε))] a.val A) (db : Lowering [(X, (⊥ : ε))] b.val A),
      da.denote J M = db.denote J M

/-- Evaluate a typed source hom representative by choosing a native
loop-free derivation and removing the singleton's extra unit. -/
noncomputable def homRepresentative {X A : τ} {e : ε}
    (a : TypedExpr Φ [(X, ⊥)] A e) : Arrow J M X A :=
  J.map (singletonInput M X) ≫
    (Classical.choice (nonempty_lowering (J := J) (M := M) a.prop)).denote J M

/-- The concrete native denotation descends along the source quotient when
it respects the source equations at the common bound e. -/
noncomputable def homMap {X A : τ} {e : ε} (h : RespectsSourceEqv (Φ := Φ) J M e) :
    Hom Φ X A e → Arrow J M X A :=
  Quotient.lift (homRepresentative J M) (fun a b related =>
    congrArg (fun f => J.map (singletonInput M X) ≫ f) (h a b related _ _))

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native
