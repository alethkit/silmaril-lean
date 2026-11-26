module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Domain.Defs

/-! # Interpretations of the generated domain in specified type coordinates -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation.Domain

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w x

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {C : Type w} [CategoryTheory.Category.{x} C] {X : τ → C}

local notation "Obj" => ofType (Seed)

/-- Express a domain arrow in the specified target objects. -/
def mapInCoordinates (F : Category Seed ⥤ C) (objIso : ∀ A : τ, F.obj (Obj A) ≅ X A)
    {A B : τ} (f : Obj A ⟶ Obj B) : X A ⟶ X B :=
  (objIso A).inv ≫ F.map f ≫ (objIso B).hom

variable [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]

/-- The selected operations and typed primitives are preserved on the generated
domain. Copair preservation follows from the injection equations. -/
structure Interpretation (T : Coordinates X) (instruction : ∀ p : Φ,
    X (instrSrc p) ⟶ X (instrTrg p)) where
  functor : Category Seed ⥤ C
  objIso : ∀ A : τ, functor.obj (Obj A) ≅ X A
  discard (A : τ) : mapInCoordinates Seed functor objIso (Domain.discard Seed A) = T.discard A
  fst (A B : τ) : mapInCoordinates Seed functor objIso (Domain.fst Seed A B) = T.fst A B
  snd (A B : τ) : mapInCoordinates Seed functor objIso (Domain.snd Seed A B) = T.snd A B
  copy (A : τ) : mapInCoordinates Seed functor objIso (diagonal Seed A) = T.copy A
  inl (A B : τ) : mapInCoordinates Seed functor objIso (Domain.inl Seed A B) =
    coprod.inl ≫ (T.sumIso A B).inv
  inr (A B : τ) : mapInCoordinates Seed functor objIso (Domain.inr Seed A B) =
    coprod.inr ≫ (T.sumIso A B).inv
  left (Y : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    mapInCoordinates Seed functor objIso (whiskerLeft Seed Y f) =
      (T.tensorIso Y A).hom ≫ (X Y ◁ mapInCoordinates Seed functor objIso f) ≫ (T.tensorIso Y B).inv
  right (Y : τ) {A B : τ} (f : Obj A ⟶ Obj B) :
    mapInCoordinates Seed functor objIso (whiskerRight Seed Y f) =
      (T.tensorIso A Y).hom ≫ (mapInCoordinates Seed functor objIso f ▷ X Y) ≫ (T.tensorIso B Y).inv
  iterate {A B : τ} (f : Obj A ⟶ Obj (coprod B A)) :
    mapInCoordinates Seed functor objIso (iterateSum Seed f) =
      CategoryTheory.iterate (mapInCoordinates Seed functor objIso f ≫ (T.sumIso B A).hom)
  primitive (p : Φ) : mapInCoordinates Seed functor objIso (Domain.primitive Seed p) = instruction p

variable {T : Coordinates X} {instruction : ∀ p : Φ, X (instrSrc p) ⟶ X (instrTrg p)}

/-- A preserving interpretation of the ambient quotient restricts to the
generated domain. The domain interface also permits functors defined there directly. -/
def Interpretation.restrict (F : Singleton.TypeCategory Seed ⥤ C)
    (objIso : ∀ A : τ, F.obj (Singleton.ofType Seed A) ≅ X A)
    (h : Preserves Seed F objIso T)
    (hp : ∀ p, Generation.mapInCoordinates Seed F objIso (Generation.primitive Seed p) = instruction p) :
    Interpretation Seed T instruction where
  functor := generatedInclusion Seed ⋙ F
  objIso := objIso
  discard := h.discard
  fst := h.fst
  snd := h.snd
  copy := h.copy
  inl := h.inl
  inr := h.inr
  left := fun Y {_ _} f => h.left Y ((generatedInclusion Seed).map f)
  right := fun Y {_ _} f => h.right Y ((generatedInclusion Seed).map f)
  iterate f := h.iterate ((generatedInclusion Seed).map f)
  primitive := hp

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation.Domain
