module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Defs

/-! # Generators and comparison coordinates for joined singleton computations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType sumCofan whiskerLeftFunctor whiskerRightFunctor
  iterateSum discardArrow productFst productSnd diagonalArrow)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open scoped MonoidalCategory

universe u v w x y z

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)

/-- The typed primitive consumes its input and returns its result once. -/
abbrev primitive (p : Φ) : Obj (instrSrc p) ⟶ Obj (instrTrg p) :=
  (projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.primitiveReturn p)

/-- Closure of the typed structural and primitive arrows under the
computation operations of the joined singleton category. -/
inductive Generated : {A B : τ} → (Obj A ⟶ Obj B) → Prop where
  | id (A : τ) : Generated (𝟙 (Obj A))
  | comp {A B D : τ} {f : Obj A ⟶ Obj B} {g : Obj B ⟶ Obj D} :
      Generated f → Generated g → Generated (f ≫ g)
  | inv {A B : τ} (i : Obj A ≅ Obj B) : Generated i.hom → Generated i.inv
  | discard (A : τ) : Generated (discardArrow (Seed) A)
  | fst (A B : τ) : Generated (productFst (Seed) A B)
  | snd (A B : τ) : Generated (productSnd (Seed) A B)
  | copy (A : τ) : Generated (diagonalArrow (Seed) (Obj A))
  | primitive (p : Φ) : Generated (Uniqueness.primitive (τ := τ) p)
  | initial {A : τ} (f : Obj (Silmaril.empty : τ) ⟶ Obj A) : Generated f
  | inl (A B : τ) : Generated (sumCofan (Seed) A B).inl
  | inr (A B : τ) : Generated (sumCofan (Seed) A B).inr
  | copair {A B D : τ} {f : Obj A ⟶ Obj D} {g : Obj B ⟶ Obj D} :
      Generated f → Generated g → Generated (exactCopair (Seed) f g)
  | left (X : τ) {A B : τ} {f : Obj A ⟶ Obj B} :
      Generated f → Generated ((whiskerLeftFunctor (Seed) (Obj X)).map f)
  | right (X : τ) {A B : τ} {f : Obj A ⟶ Obj B} :
      Generated f → Generated ((whiskerRightFunctor (Seed) (Obj X)).map f)
  | iterate {A B : τ} {f : Obj A ⟶ Obj (coprod B A)} :
      Generated f → Generated (iterateSum (Seed) f)

/-- Generated arrows as a multiplicative morphism property. -/
def generatedArrows : MorphismProperty (TypeCategory (τ := τ) (Φ := Φ)) :=
  fun A B f => Generated (A := (show τ from A.as)) (B := (show τ from B.as)) f

instance generatedArrows_multiplicative : (generatedArrows (τ := τ) (Φ := Φ)).IsMultiplicative where
  id_mem A := Generated.id (show τ from A.as)
  comp_mem _ _ hf hg := Generated.comp hf hg

/-- The wide subcategory with just the generated arrows. -/
abbrev generatedInclusion :
    WideSubcategory (generatedArrows (τ := τ) (Φ := Φ)) ⥤ TypeCategory (τ := τ) (Φ := Φ) :=
  wideSubcategoryInclusion _

section Target

variable {C : Type w} [Category.{x} C] [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]
  {X : τ → C}

/-- The target's chosen structure in the coordinates of the interpreted types.
For a Freyd interpretation the four value maps are the images of the
corresponding Cartesian maps. -/
structure Coordinates (X : τ → C) where
  tensorIso (A B : τ) : X (product A B) ≅ X A ⊗ X B
  sumIso (A B : τ) : X (coprod A B) ≅ X A ⨿ X B
  initial : IsInitial (X (Silmaril.empty : τ))
  discard (A : τ) : X A ⟶ X (Silmaril.unit : τ)
  fst (A B : τ) : X (product A B) ⟶ X A
  snd (A B : τ) : X (product A B) ⟶ X B
  copy (A : τ) : X A ⟶ X (product A A)

open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open CfgEta.TypeCategory.ConstructorReification (unitMap fstMap sndMap)
open Paper.SingletonReification (packedDiagonal)

/-- The chosen comparisons supplied by a typed Cartesian value interpretation
and its strong premonoidal, coproduct-preserving inclusion. -/
noncomputable def Coordinates.ofModel {V : Type y} [Category.{z} V]
    [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
    (J : V ⥤ C) [Functor.StrongPremonoidal J] [PreservesFiniteCoproducts J]
    (M : TypeModel τ V) : Coordinates (fun A => J.obj (M.obj A)) where
  tensorIso A B := J.mapIso (M.productIso A B) ≪≫
    (Functor.StrongPremonoidal.tensorIso (J := J) (M.obj A) (M.obj B)).symm
  sumIso A B := J.mapIso (M.coprodIso A B) ≪≫
    (PreservesColimitPair.iso J (M.obj A) (M.obj B)).symm
  initial := M.emptyIsInitial.isInitialObj J
  discard A := J.map (unitMap M A)
  fst A B := J.map (fstMap M A B)
  snd A B := J.map (sndMap M A B)
  copy A := J.map (packedDiagonal M A)

variable (F : TypeCategory (τ := τ) (Φ := Φ) ⥤ C) (objIso : ∀ A : τ, F.obj (Obj A) ≅ X A)

/-- Compare arrows after transporting the functor's source and target objects. -/
def mapInCoordinates {A B : τ} (f : Obj A ⟶ Obj B) : X A ⟶ X B :=
  (objIso A).inv ≫ F.map f ≫ (objIso B).hom

/-- Local structural preservation at the named source and target coordinates.
The iterator equation includes the exact-to-chosen sum conversion. -/
structure Preserves (T : Coordinates X) : Prop where
  discard (A : τ) : mapInCoordinates F objIso (discardArrow (Seed) A) = T.discard A
  fst (A B : τ) : mapInCoordinates F objIso (productFst (Seed) A B) = T.fst A B
  snd (A B : τ) : mapInCoordinates F objIso (productSnd (Seed) A B) = T.snd A B
  copy (A : τ) : mapInCoordinates F objIso (diagonalArrow (Seed) (Obj A)) = T.copy A
  inl (A B : τ) : mapInCoordinates F objIso (sumCofan (Seed) A B).inl =
    CategoryTheory.Limits.coprod.inl ≫ (T.sumIso A B).inv
  inr (A B : τ) : mapInCoordinates F objIso (sumCofan (Seed) A B).inr =
    CategoryTheory.Limits.coprod.inr ≫ (T.sumIso A B).inv
  left (Y : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    mapInCoordinates F objIso ((whiskerLeftFunctor (Seed) (Obj Y)).map f) =
      (T.tensorIso Y A).hom ≫ (X Y ◁ mapInCoordinates F objIso f) ≫ (T.tensorIso Y B).inv
  right (Y : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    mapInCoordinates F objIso ((whiskerRightFunctor (Seed) (Obj Y)).map f) =
      (T.tensorIso A Y).hom ≫ (mapInCoordinates F objIso f ▷ X Y) ≫ (T.tensorIso B Y).inv
  iterate {A B : τ} (f : Obj A ⟶ Obj (coprod B A)) :
    mapInCoordinates F objIso (iterateSum (Seed) f) =
      CategoryTheory.iterate (mapInCoordinates F objIso f ≫ (T.sumIso B A).hom)

end Target

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness
