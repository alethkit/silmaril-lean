module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs

/-! # Generators and comparison coordinates for joined singleton computations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType sumCofan whiskerLeftFunctor whiskerRightFunctor
  iterateSum discardArrow productFst productSnd diagonalArrow)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open scoped MonoidalCategory

universe u v w x

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)

abbrev primitive := Paper.Extension.Singleton.Generation.primitive (Seed)

abbrev Generated := @Paper.Extension.Singleton.Generation.Generated _ _ _ _ (Seed)

namespace Generated
export Paper.Extension.Singleton.Generation.Generated
  (id comp inv discard fst snd copy primitive initial inl inr copair left right iterate rec recOn casesOn)
end Generated

abbrev generatedArrows := Paper.Extension.Singleton.Generation.generatedArrows (Seed)

abbrev generatedArrows_multiplicative :=
  Paper.Extension.Singleton.Generation.generatedArrows_multiplicative (Seed)

abbrev generatedInclusion := Paper.Extension.Singleton.Generation.generatedInclusion (Seed)

section Target

variable {C : Type w} [Category.{x} C] [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]
  {X : τ → C}

abbrev Coordinates (X : τ → C) := Paper.Extension.Singleton.Generation.Coordinates X

namespace Coordinates
export Paper.Extension.Singleton.Generation.Coordinates (mk ofModel)
end Coordinates

variable (F : TypeCategory (τ := τ) (Φ := Φ) ⥤ C) (objIso : ∀ A : τ, F.obj (Obj A) ≅ X A)

abbrev mapInCoordinates {A B : τ} (f : Obj A ⟶ Obj B) : X A ⟶ X B :=
  Paper.Extension.Singleton.Generation.mapInCoordinates (Seed) F objIso f

abbrev Preserves (T : Coordinates X) : Prop :=
  Paper.Extension.Singleton.Generation.Preserves (Seed) F objIso T

namespace Preserves
export Paper.Extension.Singleton.Generation.Preserves (mk)
end Preserves

end Target

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Uniqueness
