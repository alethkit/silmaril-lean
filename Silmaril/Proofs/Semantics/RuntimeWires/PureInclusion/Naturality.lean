module

public import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Interpretation
public import Silmaril.Semantics.RuntimeWires.PureInclusion.Values

public section

namespace Silmaril.RuntimeWires.Proofs.PureInclusion

open CategoryTheory MonoidalCategory
open Presentation RuntimeCoherence
open scoped MonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "R" => runtime G
local notation "V" => valueWord (G := G)
local notation "σ" => crossingWord (G := G)

/-- The isomorphism on words has the representative used by Figure 9. -/
theorem crossingWord_slide (A : List G.Obj) :
    (σ A).hom = Diagram.Presented.ofTerm (slideRight (G := G) A) := by
  induction A with
  | nil => exact crossing_nil.eq
  | cons x A ih =>
    apply SameArrow.eq
    refine (crossing_cons x A).trans ?_
    have e := (SameArrow.refl ((crossing x).hom ▷ V A)).join_congr
      ((SameArrow.of_eq ih).whiskerLeft (X := V [x]) rfl) (by runtime_word) rfl
    exact e.trans (.of_eq (SameArrow.join_eq rfl))

private theorem crossTensor_natural {X Y U W : Runtime G}
    (f : X ⟶ Y) (g : U ⟶ W) {sX : R ⊗ X ≅ X ⊗ R} {sY : R ⊗ Y ≅ Y ⊗ R}
    {sU : R ⊗ U ≅ U ⊗ R} {sW : R ⊗ W ≅ W ⊗ R}
    (hf : sX.hom ≫ f ▷ R = R ◁ f ≫ sY.hom)
    (hg : sU.hom ≫ g ▷ R = R ◁ g ≫ sW.hom) :
    (crossTensor sX sU).hom ≫ (f ⊗ₘ g) ▷ R =
      R ◁ (f ⊗ₘ g) ≫ (crossTensor sY sW).hom := by
  simp only [← tensorHom_id, ← id_tensorHom] at hf hg
  have hn₁ : (𝟙 X ⊗ₘ sU.hom) ≫ (f ⊗ₘ (g ⊗ₘ 𝟙 R)) =
      (f ⊗ₘ (𝟙 R ⊗ₘ g)) ≫ (𝟙 Y ⊗ₘ sW.hom) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hg]
  have hn₂ : (sX.hom ⊗ₘ 𝟙 U) ≫ ((f ⊗ₘ 𝟙 R) ⊗ₘ g) =
      ((𝟙 R ⊗ₘ f) ⊗ₘ g) ≫ (sY.hom ⊗ₘ 𝟙 W) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hf]
  simp only [crossTensor, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    Category.assoc, ← tensorHom_id, ← id_tensorHom]
  rw [← associator_inv_naturality f g (𝟙 R), reassoc_of% hn₁,
    ← associator_naturality_assoc f (𝟙 R) g, reassoc_of% hn₂,
    ← associator_inv_naturality_assoc (𝟙 R) f g]

/-- Runtime crossings are natural for every pure diagram. -/
theorem term_natural {A B : List G.Obj} (f : Diagram G.pure A B) :
    (σ A).hom ≫ pureTerm f ▷ R = R ◁ pureTerm f ≫ (σ B).hom := by
  induction f with
  | id A =>
    change (σ A).hom ≫ (𝟙 (V A) ▷ R) = R ◁ 𝟙 (V A) ≫ (σ A).hom
    simp
  | gen e =>
    rw [crossingWord_slide, crossingWord_slide]
    exact Quotient.sound (Diagram.Congruence.equation (Relations.pureRight e))
  | comp f g hf hg =>
    simp only [pureTerm, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% hf, hg]
  | @tensor A B C D f g hf hg =>
    have hA := (crossing_append A C).trans (crossTensor_hom (σ A) (σ C)).symm
    have hB := (crossing_append B D).trans (crossTensor_hom (σ B) (σ D)).symm
    have hp := tensor_term f g
    exact ((hA.comp (hp.whiskerRight rfl)).trans
      ((SameArrow.of_eq (crossTensor_natural (pureTerm f) (pureTerm g) hf hg)).trans
        ((hp.symm.whiskerLeft rfl).comp hB.symm))).eq

theorem pureValues_tensor {A B C D : Pure G} (f : A ⟶ B) (g : C ⟶ D) :
    (pureValues G).map (f ⊗ₘ g) ≈ₐ (pureValues G).map f ⊗ₘ (pureValues G).map g :=
  Quotient.inductionOn₂ f g tensor_term

theorem pureValues_natural {X Y : Pure G} (f : X ⟶ Y) :
    (σ X.word).hom ≫ (pureValues G).map f ▷ R =
      R ◁ (pureValues G).map f ≫ (σ Y.word).hom :=
  Quotient.inductionOn f term_natural

end Silmaril.RuntimeWires.Proofs.PureInclusion
