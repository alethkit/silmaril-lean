module

public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Whiskering

public section

namespace Silmaril.RuntimeWires.Proofs.RuntimeCoherence

open CategoryTheory PremonoidalCategory
open Presentation
open scoped MonoidalCategory SameArrow

universe u v

variable {G : EffectfulPolygraph.{u,v}}
local notation "C" => Computations G

namespace Computation

theorem left_id (A B : C) : A ◁ 𝟙 B = 𝟙 (A ⊗ B) :=
  (A.whiskerLeft).map_id B

theorem left_comp (A : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    A ◁ (f ≫ g) = (A ◁ f) ≫ (A ◁ g) :=
  (A.whiskerLeft).map_comp f g

theorem right_id (A B : C) : 𝟙 A ▷ B = 𝟙 (A ⊗ B) :=
  (B.whiskerRight).map_id A

theorem right_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (A : C) :
    (f ≫ g) ▷ A = (f ▷ A) ≫ (g ▷ A) :=
  (A.whiskerRight).map_comp f g

theorem left_cast (A : C) {X Y : C} (h : X = Y) :
    A ◁ eqToHom h = eqToHom (congrArg (A ⊗ ·) h) :=
  eqToHom_map (A.whiskerLeft) h

theorem right_cast {X Y : C} (h : X = Y) (A : C) :
    eqToHom h ▷ A = eqToHom (congrArg (· ⊗ A) h) :=
  eqToHom_map (A.whiskerRight) h

theorem assoc_hom (A B D : C) : (α_ A B D).hom = eqToHom (Computations.concat_assoc A B D) :=
  rfl

theorem left_hom (A : C) : (λ_ A).hom = eqToHom (Computations.empty_concat A) := rfl

theorem right_hom (A : C) : (ρ_ A).hom = eqToHom (Computations.concat_empty A) := rfl

theorem cast_central {A B : C} (h : A = B) : IsCentral (eqToHom h) := by
  subst h
  constructor <;> intro X Y f <;>
    simp only [eqToHom_refl, leftTensor, rightTensor, left_id, right_id,
      Category.id_comp, Category.comp_id]

theorem square {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (h : (show A.boundary ⟶ B.boundary from f) ≈ₐ (show A'.boundary ⟶ B'.boundary from g))
    (a : A = A') (b : B = B') : f ≫ eqToHom b = eqToHom a ≫ g := by
  subst a
  subst b
  simpa using h.eq

theorem naturality_left {X Y : C} (f : X ⟶ Y) (Z W : C) :
    ((f ▷ Z) ▷ W) ≫ (α_ Y Z W).hom = (α_ X Z W).hom ≫ f ▷ (Z ⊗ W) :=
  square (right_right f Z W) (Computations.concat_assoc X Z W) (Computations.concat_assoc Y Z W)

theorem naturality_middle (X : C) {Y Z : C} (f : Y ⟶ Z) (W : C) :
    ((X ◁ f) ▷ W) ≫ (α_ X Z W).hom = (α_ X Y W).hom ≫ X ◁ (f ▷ W) :=
  square (left_right X f W) (Computations.concat_assoc X Y W) (Computations.concat_assoc X Z W)

theorem naturality_right (X Y : C) {Z W : C} (f : Z ⟶ W) :
    ((X ⊗ Y) ◁ f) ≫ (α_ X Y W).hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) :=
  square (left_left X Y f) (Computations.concat_assoc X Y Z) (Computations.concat_assoc X Y W)

theorem naturality_leftUnitor {X Y : C} (f : X ⟶ Y) :
    (𝟙_ C) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f :=
  square (left_unit f) (Computations.empty_concat X) (Computations.empty_concat Y)

theorem naturality_rightUnitor {X Y : C} (f : X ⟶ Y) :
    f ▷ (𝟙_ C) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f :=
  square (right_unit f) (Computations.concat_empty X) (Computations.concat_empty Y)

theorem pentagon (W X Y Z : C) : MonoidalCategory.Pentagon W X Y Z := by
  simp only [MonoidalCategory.Pentagon, assoc_hom, right_cast, left_cast, eqToHom_trans]

theorem triangle (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  simp only [assoc_hom, left_hom, right_hom, left_cast, right_cast, eqToHom_trans]

end Computation
end Silmaril.RuntimeWires.Proofs.RuntimeCoherence
