module

public import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Centrality
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Premonoidal

public section

namespace Silmaril.RuntimeWires.Proofs.PureInclusion

open CategoryTheory MonoidalCategory
open Presentation RuntimeCoherence
open scoped MonoidalCategory SameArrow

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "R" => runtime G
local notation "J" => pureInclusion G
local notation "U" => pureValues G

theorem map_right {X Y : Pure G} (f : X ⟶ Y) (Z : Pure G) :
    (J).map f ▷ (J).obj Z = (J).map (f ▷ Z) := by
  have h : (U).map (f ▷ Z) ≈ₐ (U).map f ▷ (U).obj Z := by
    exact (pureValues_tensor f (𝟙 Z)).trans (.of_eq
      ((congrArg ((U).map f ⊗ₘ ·) ((U).map_id Z)).trans
        (tensorHom_id ((U).map f) ((U).obj Z))))
  exact ((right_normal ((J).map f) ((J).obj Z)).trans
    ((whisker_left_right R ((U).map f) ((U).obj Z)).trans (h.symm.whiskerLeft rfl))).eq

theorem map_left (X : Pure G) {Y Z : Pure G} (f : Y ⟶ Z) :
    (J).obj X ◁ (J).map f = (J).map (X ◁ f) := by
  have h : (U).map (X ◁ f) ≈ₐ (U).obj X ◁ (U).map f := by
    exact (pureValues_tensor (𝟙 X) f).trans (.of_eq
      ((congrArg (· ⊗ₘ (U).map f) ((U).map_id X)).trans
        (id_tensorHom ((U).obj X) ((U).map f))))
  exact ((left_pure ((J).obj X) f).trans
    ((whisker_left_left R ((U).obj X) ((U).map f)).trans (h.symm.whiskerLeft rfl))).eq

theorem map_associator (X Y Z : Pure G) :
    (J).map (α_ X Y Z).hom = (α_ ((J).obj X) ((J).obj Y) ((J).obj Z)).hom :=
  eqToHom_map J (Diagram.Presented.concat_assoc X Y Z)

theorem map_leftUnitor (X : Pure G) :
    (J).map (λ_ X).hom = (λ_ ((J).obj X)).hom :=
  eqToHom_map J (Diagram.Presented.empty_concat X)

theorem map_rightUnitor (X : Pure G) :
    (J).map (ρ_ X).hom = (ρ_ ((J).obj X)).hom :=
  eqToHom_map J (Diagram.Presented.concat_empty X)

@[expose, instance_reducible] def strong (G : EffectfulPolygraph.{u,v}) :
    Functor.StrongPremonoidal (pureInclusion G) where
  unitIso := Iso.refl _
  tensorIso _ _ := Iso.refl _
  tensor_naturality_left {_ _} f Z :=
    (Category.comp_id _).trans ((map_right f Z).trans (Category.id_comp _).symm)
  tensor_naturality_right X {_ _} f :=
    (Category.comp_id _).trans ((map_left X f).trans (Category.id_comp _).symm)
  associativity X Y Z := by
    let A := (pureInclusion G).obj X
    let B := (pureInclusion G).obj Y
    let C := (pureInclusion G).obj Z
    let a := (α_ A B C).hom
    let b : (A ⊗ B) ⊗ C ⟶ A ⊗ (B ⊗ C) := (pureInclusion G).map (α_ X Y Z).hom
    have h₁ : a ≫ A ◁ 𝟙 (B ⊗ C) ≫ 𝟙 (A ⊗ (B ⊗ C)) = a := by simp
    have h₂ : 𝟙 (A ⊗ B) ▷ C ≫ 𝟙 ((A ⊗ B) ⊗ C) ≫ b = b := by simp
    exact h₁.trans ((map_associator X Y Z).symm.trans h₂.symm)
  left_unitality X := by
    let A := (pureInclusion G).obj X
    let f : (𝟙_ (Computations G)) ⊗ A ⟶ A := (pureInclusion G).map (λ_ X).hom
    have h : 𝟙 (𝟙_ (Computations G)) ▷ A ≫ 𝟙 ((𝟙_ (Computations G)) ⊗ A) ≫ f = f := by simp
    exact h.trans (map_leftUnitor X)
  right_unitality X := by
    let A := (pureInclusion G).obj X
    let f : A ⊗ (𝟙_ (Computations G)) ⟶ A := (pureInclusion G).map (ρ_ X).hom
    have h : A ◁ 𝟙 (𝟙_ (Computations G)) ≫ 𝟙 (A ⊗ (𝟙_ (Computations G))) ≫ f = f := by simp
    exact h.trans (map_rightUnitor X)
  map_central {_ _} f := image_central f

end Silmaril.RuntimeWires.Proofs.PureInclusion
