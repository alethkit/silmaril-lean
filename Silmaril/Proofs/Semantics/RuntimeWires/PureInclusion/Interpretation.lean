module

public import Silmaril.Semantics.RuntimeWires.PureInclusion.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Crossing

public section

namespace Silmaril.RuntimeWires.Proofs.PureInclusion

open CategoryTheory MonoidalCategory
open Presentation RuntimeCoherence
open scoped MonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "V" => valueWord (G := G)

theorem tensor_term {A B C D : List G.Obj} (f : Diagram G.pure A B) (g : Diagram G.pure C D) :
    pureTerm (.tensor f g) ≈ₐ pureTerm f ⊗ₘ pureTerm g :=
  (SameArrow.cast_comp _).trans (SameArrow.comp_cast _)

private theorem reindex_term {A B C D : List G.Obj} (p : A = C) (q : B = D)
    (f : Diagram G.pure A B) : pureTerm (Diagram.reindex p q f) ≈ₐ pureTerm f := by
  subst p
  subst q
  exact SameArrow.refl _

private theorem tensor_assoc {X Y Z X' Y' Z' : Runtime G}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g) ⊗ₘ h ≈ₐ f ⊗ₘ g ⊗ₘ h := by
  calc
    _ ≈ₐ ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom :=
      (SameArrow.comp_cast (Diagram.Presented.concat_assoc X' Y' Z')).symm
    _ ≈ₐ (α_ X Y Z).hom ≫ (f ⊗ₘ g ⊗ₘ h) := .of_eq (associator_naturality f g h)
    _ ≈ₐ _ := SameArrow.cast_comp (Diagram.Presented.concat_assoc X Y Z)

/-- Interpretation descends through the strict monoidal equations of the pure presentation. -/
theorem respect {A B : List G.Obj} {f g : Diagram G.pure A B}
    (h : Diagram.Congruence (fun _ _ => False) f g) : pureTerm f = pureTerm g := by
  induction h with
  | equation h => exact h.elim
  | refl => rfl
  | symm _ h => exact h.symm
  | trans _ _ h k => exact h.trans k
  | comp _ _ h k => exact congrArg₂ CategoryStruct.comp h k
  | tensor _ _ h k => simp only [pureTerm, h, k]
  | id_comp => exact Category.id_comp _
  | comp_id => exact Category.comp_id _
  | comp_assoc => exact Category.assoc _ _ _
  | tensor_id A B =>
    exact ((tensor_term (.id A) (.id B)).trans
      ((SameArrow.of_eq (id_tensorHom_id _ _)).trans (.id (word_append A B).symm))).eq
  | tensor_comp f g h k =>
    exact ((tensor_term (.comp f g) (.comp h k)).trans
      ((SameArrow.of_eq (tensorHom_comp_tensorHom (pureTerm f) (pureTerm h)
        (pureTerm g) (pureTerm k)).symm).trans
        ((tensor_term f h).symm.comp (tensor_term g k).symm))).eq
  | tensor_unit_left f =>
    apply SameArrow.eq
    refine (reindex_term _ _ _).trans ((tensor_term (.id []) f).trans ?_)
    change (𝟙 (𝟙_ (Runtime G)) ⊗ₘ pureTerm f) ≈ₐ pureTerm f
    exact (SameArrow.of_eq (id_tensorHom _ _)).trans (whiskerLeft_unit (pureTerm f))
  | tensor_unit_right f =>
    apply SameArrow.eq
    refine (reindex_term _ _ _).trans ((tensor_term f (.id [])).trans ?_)
    change (pureTerm f ⊗ₘ 𝟙 (𝟙_ (Runtime G))) ≈ₐ pureTerm f
    exact (SameArrow.of_eq (tensorHom_id _ _)).trans (whiskerRight_unit (pureTerm f))
  | tensor_assoc f g h =>
    exact ((reindex_term _ _ _).trans ((tensor_term (.tensor f g) h).trans
      (((tensor_term f g).tensor (.refl _)).trans
        ((tensor_assoc (pureTerm f) (pureTerm g) (pureTerm h)).trans
          (((SameArrow.refl _).tensor (tensor_term g h).symm).trans
            (tensor_term f (.tensor g h)).symm))))).eq

end Silmaril.RuntimeWires.Proofs.PureInclusion
