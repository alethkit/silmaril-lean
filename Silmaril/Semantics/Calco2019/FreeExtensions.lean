module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Profunctor.Basic

/-! # Free extensions (CALCO 2019, Article 13, §3) -/

@[expose] public section

universe u v w u' v'

namespace Silmaril.Calco2019

open CategoryTheory

/-- Definition 1. A `Cᵒᵖ × D`-indexed bimodule. Mathlib orders the covariant
category first. -/
abbrev Bimodule (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D] :=
  Profunctor.{w} D C

namespace Bimodule

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (O : Bimodule C D) {A : C} {B V : D}

/-- The underlying set of bimodule morphisms. -/
abbrev Hom (A : C) (X : D) := (O.obj X).obj (Opposite.op A)

/-- Precompose a bimodule morphism by a map in the contravariant category. -/
def pre {A' : C} (f : A' ⟶ A) (g : O.Hom A B) : O.Hom A' B :=
  (O.obj B).map f.op g

/-- Postcompose a bimodule morphism by a map in the covariant category. -/
def post (g : O.Hom A B) (h : B ⟶ V) : O.Hom A V :=
  (O.map h).app (Opposite.op A) g

theorem post_comp {X : D} (g : O.Hom A B) (h : B ⟶ V) (k : V ⟶ X) :
    O.post g (h ≫ k) = O.post (O.post g h) k := by
  simp [post]

/-- The universal property of Definition 2 for specified legs. -/
def IsFreeExtension (e : O.Hom A V) (f : B ⟶ V) : Prop :=
  ∀ (X : D) (g : O.Hom A X) (h : B ⟶ X),
    ∃! k : V ⟶ X, O.post e k = g ∧ f ≫ k = h

/-- The universal property of Definition 3 for a specified generator. -/
def IsFreeObject (e : O.Hom A V) : Prop :=
  ∀ (X : D) (g : O.Hom A X), ∃! k : V ⟶ X, O.post e k = g

/-- Definition 2. A free extension of `B` by `A`. -/
structure FreeExtension (A : C) (B : D) where
  pt : D
  generator : O.Hom A pt
  inclusion : B ⟶ pt
  isFreeExtension : O.IsFreeExtension generator inclusion

/-- Definition 3. A free object on `A`. -/
structure FreeObject (A : C) where
  pt : D
  generator : O.Hom A pt
  isFreeObject : O.IsFreeObject generator

end Bimodule
end Silmaril.Calco2019
