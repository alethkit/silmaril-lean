module

public import Silmaril.Semantics.Calco2019.Thms
public import Silmaril.Semantics.Categories.Thms
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# CALCO iteration and complete Elgot semantics

Total guardedness allows every loop body. The Freyd interface also has a
separate context-strength law, which is outside the CALCO Conway bundle.
-/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

/-- The objectwise coproducts in the category of types, with the return summand on the left. -/
def typeCoproducts : Coproducts (Type u) where
  sum := Sum
  inl := ↾Sum.inl
  inr := ↾Sum.inr
  isColimit := Types.binaryCoproductColimit

@[simp] theorem Coproducts.selected_desc {K : Type u} [Category.{v} K]
    [HasBinaryCoproducts K] {X Y Z : K} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (ofHasBinaryCoproducts K).desc f g = coprod.desc f g := by
  apply (ofHasBinaryCoproducts K).hom_ext
  · rw [inl_desc]; exact (coprod.inl_desc f g).symm
  · rw [inr_desc]; exact (coprod.inr_desc f g).symm

/-- Read the existing categorical iteration operator with CALCO's total guard. -/
noncomputable def categoricalFixpoints (K : Type u) [Category.{v} K]
    [HasFiniteCoproducts K] [Iteration K] [ElgotCategory K] :
    (Guardedness.greatest (Coproducts.ofHasBinaryCoproducts K)).Fixpoints where
  iterate f _ := CategoryTheory.iterate f
  fixpoint {X Y} f _ := by
    change f ≫ (Coproducts.ofHasBinaryCoproducts K).desc (𝟙 Y)
      (CategoryTheory.iterate (X := X) (Y := Y) f) = CategoryTheory.iterate f
    rw [Coproducts.selected_desc]
    exact ElgotCategory.unfold f

section Types

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- Put a monadic function into the Kleisli category used by the SSA denotations. -/
abbrev computation {A B : Type u} (f : A → m B) :
    Kleisli.mk (ofTypeMonad m) A ⟶ Kleisli.mk (ofTypeMonad m) B :=
  kleisliArrow (↾f)

/-- The inherited coproduct and the SSA-selected coproduct use the same cocone up to its
canonical comparison. This arrow takes a sum-valued body to the input of SSA iteration. -/
noncomputable def sumToSelected (A B : Type u) :
    (typeCoproducts.kleisli (ofTypeMonad m)).sum (.mk _ A) (.mk _ B) ⟶
      (Kleisli.mk (ofTypeMonad m) A) ⨿ (Kleisli.mk (ofTypeMonad m) B) :=
  (Kleisli.Type.coprodIsoSum m (.mk _ A) (.mk _ B)).inv

end Types

end Silmaril.Calco2019
