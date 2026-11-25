module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs

/-! # Transport data for retained-context LambdaSSA -/

@[expose] public section

open Silmaril
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CfgEta CfgEta.TypeCategory CfgEta.TypeCategory.ConstructorReification
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate retainLeft bind caseWithContext splitMapCoprod)

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained

section Syntactic

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The diagonal on a syntactic type. -/
theorem duplicateBranches (X : τ) :
    ValueBranches [X] (.br 0 (.pair (.var 0) (.var 0)) : Region Φ) [Silmaril.product X X] :=
  .br rfl (.pair (.var rfl) (.var rfl))

def duplicateArrow (X : τ) :
    ofType (Φ := Φ) (Γ := []) X ⟶ ofType (Silmaril.product X X) :=
  ofRegion (duplicateBranches X)

def distributorRegion : Region Φ :=
  .let₂ (.var 0) (.case (.var 0)
    (.br 0 (.inl (.pair (.var 2) (.var 0))))
    (.br 0 (.inr (.pair (.var 2) (.var 0)))))

theorem distributorRegion_typed (X A B : τ) :
    ValueBranches [Silmaril.product X (Silmaril.coprod A B)] (distributorRegion : Region Φ)
      [Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)] :=
  .let₂ (.var (i := 0) rfl) (.case (.var (i := 0) rfl)
    (.br rfl (.inl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))))
    (.br rfl (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))))

end Syntactic

section Transport

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ TypeCategory Φ ([] : VCtx τ)) (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) (Γ := []) A)
  {X A B D : τ}

/-- Reindex an interpreted computation at the two exact syntactic type objects. -/
def transportHom (f : J.obj (M.obj X) ⟶ J.obj (M.obj A)) :
    ofType (Φ := Φ) (Γ := []) X ⟶ ofType A :=
  (objIso X).inv ≫ f ≫ (objIso A).hom

end Transport

section PackedCase

variable {τ : Type u} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)
  {A B D : τ}

/-- The distributor between interpreted exact product and sum types. -/
noncomputable def packedDistributor [DistributiveTensor V] (X A B : τ) :
    M.obj (Silmaril.product X (Silmaril.coprod A B)) ⟶
      M.obj (Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)) :=
  (M.productIso X (Silmaril.coprod A B)).hom ≫ (M.obj X ◁ (M.coprodIso A B).hom) ≫
    (DistributiveTensor.leftIso (M.obj X) (M.obj A) (M.obj B)).inv ≫
    coprod.map (M.productIso X A).inv (M.productIso X B).inv ≫ (M.coprodIso _ _).inv

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

variable {M} in
noncomputable def packedCopair (M : TypeModel τ V)
    (f : J.obj (M.obj A) ⟶ J.obj (M.obj D)) (g : J.obj (M.obj B) ⟶ J.obj (M.obj D)) :
    J.obj (M.obj (Silmaril.coprod A B)) ⟶ J.obj (M.obj D) :=
  J.map (M.coprodIso A B).hom ≫ splitMapCoprod J (M.obj A) (M.obj B) ≫ coprod.desc f g

end PackedCase

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained
