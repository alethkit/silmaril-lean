module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs

/-! # Packed source products for singleton comparisons -/

@[expose] public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

/-- Interpret a source value morphism and transport its endpoints to the singleton syntax types. -/
def reindexValueHom (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
    (comparison : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)
    (X A : τ) (f : M.obj X ⟶ M.obj A) :
    ofType (Φ := Φ) X ⟶ ofType A :=
  Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.reindexHom (τ := τ) (Φ := Φ) J M comparison (Y := X) (Z := A) (J.map f)

/-- A Cartesian pairing with its output expressed at the interpreted product type. -/
def packedPair (M : TypeModel τ V) (X A B : τ) (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B) :
    M.obj X ⟶ M.obj (product A B) :=
  CartesianMonoidalCategory.lift f g ≫ (M.productIso A B).inv

/-- The source Cartesian diagonal expressed at the interpreted product type. -/
def packedDiagonal (M : TypeModel τ V) (X : τ) : M.obj X ⟶ M.obj (product X X) :=
  packedPair M X X X (𝟙 (M.obj X)) (𝟙 (M.obj X))

/-- Apply a source value map to the left component of an interpreted product. -/
def packedWhiskerRight (M : TypeModel τ V) (R A B : τ) (f : M.obj A ⟶ M.obj B) :
    M.obj (product A R) ⟶ M.obj (product B R) :=
  (M.productIso A R).hom ≫ (f ▷ M.obj R) ≫ (M.productIso B R).inv

/-- Apply a source value map to the right component of an interpreted product. -/
def packedWhiskerLeft (M : TypeModel τ V) (R A B : τ) (f : M.obj A ⟶ M.obj B) :
    M.obj (product R A) ⟶ M.obj (product R B) :=
  (M.productIso R A).hom ≫ (M.obj R ◁ f) ≫ (M.productIso R B).inv

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
