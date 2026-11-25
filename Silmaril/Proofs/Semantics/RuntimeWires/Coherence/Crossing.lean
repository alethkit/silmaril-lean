module

public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Transport

public section

namespace Silmaril.RuntimeWires.Proofs.RuntimeCoherence

open CategoryTheory MonoidalCategory
open Presentation Diagram.Presented
open scoped SameArrow RuntimeCoherence MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "R" => runtime G
local notation "V" => valueWord (G := G)
local notation "σ" => crossingWord (G := G)

/-- Pass the runtime across two consecutive blocks. -/
@[expose] def crossTensor {X Y : Runtime G} (s : R ⊗ X ≅ X ⊗ R) (t : R ⊗ Y ≅ Y ⊗ R) :
    R ⊗ (X ⊗ Y) ≅ (X ⊗ Y) ⊗ R :=
  (α_ R X Y).symm ≪≫ (s ⊗ᵢ Iso.refl Y) ≪≫ α_ X R Y ≪≫
    (Iso.refl X ⊗ᵢ t) ≪≫ (α_ X Y R).symm

theorem crossTensor_hom {X Y : Runtime G} (s : R ⊗ X ≅ X ⊗ R) (t : R ⊗ Y ≅ Y ⊗ R) :
    (crossTensor s t).hom ≈ₐ (s.hom ▷ Y) ≫ₐ (X ◁ t.hom) := by
  let m := (s.hom ▷ Y) ≫ₐ (X ◁ t.hom)
  have h : eqToHom (concat_assoc R X Y).symm ≫ m ≫ eqToHom (concat_assoc X Y R).symm ≈ₐ m :=
    (SameArrow.cast_comp _).trans (SameArrow.comp_cast _)
  simpa only [crossTensor, m, SameArrow.join, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, id_tensorHom, Category.assoc, assoc_hom_eq, assoc_inv_eq] using h

theorem crossTensor_inv {X Y : Runtime G} (s : R ⊗ X ≅ X ⊗ R) (t : R ⊗ Y ≅ Y ⊗ R) :
    (crossTensor s t).inv ≈ₐ (X ◁ t.inv) ≫ₐ (s.inv ▷ Y) := by
  let m := (X ◁ t.inv) ≫ₐ (s.inv ▷ Y)
  have h : eqToHom (concat_assoc X Y R) ≫ m ≫ eqToHom (concat_assoc R X Y) ≈ₐ m :=
    (SameArrow.cast_comp _).trans (SameArrow.comp_cast _)
  simpa only [crossTensor, m, SameArrow.join, Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
    Iso.refl_inv, tensorHom_id, id_tensorHom, Category.assoc, assoc_hom_eq, assoc_inv_eq] using h

theorem crossing_nil : (σ []).hom ≈ₐ 𝟙 R := by
  change eqToHom (concat_empty R) ≫ eqToHom (empty_concat R).symm ≈ₐ 𝟙 R
  rw [eqToHom_trans]
  exact SameArrow.eqToHom_id _

theorem crossing_nil_inv : (σ []).inv ≈ₐ 𝟙 R :=
  (show (σ []).hom ≈ₐ (Iso.refl R).hom from crossing_nil).inv

theorem crossing_cons (x : G.Obj) (A : List G.Obj) :
    (σ (x :: A)).hom ≈ₐ ((crossing x).hom ▷ V A) ≫ₐ (V [x] ◁ (σ A).hom) :=
  crossTensor_hom (crossing x) (σ A)

/-- Splitting a braid into two consecutive crossings preserves its morphism. -/
theorem crossing_append (A B : List G.Obj) :
    (σ (A ++ B)).hom ≈ₐ ((σ A).hom ▷ V B) ≫ₐ (V A ◁ (σ B).hom) := by
  induction A with
  | nil =>
    change (σ B).hom ≈ₐ ((σ []).hom ▷ V B) ≫ₐ ((𝟙_ (Runtime G)) ◁ (σ B).hom)
    apply SameArrow.symm
    apply SameArrow.trans
      ((crossing_nil.whiskerRight rfl).join_congr (whiskerLeft_unit (σ B).hom) _ (by runtime_word))
    simpa only [id_whiskerRight] using
      (SameArrow.id_join (k := (σ B).hom) (show R ⊗ V B = R ⊗ V B from rfl))
  | cons x A ih =>
    let s := (crossing x).hom
    let a := (σ A).hom
    let b := (σ B).hom
    let p := (s ▷ V A) ▷ V B
    let q := (V [x] ◁ a) ▷ V B
    let r := (V [x] ⊗ V A) ◁ b
    have e₁ : s ▷ V (A ++ B) ≈ₐ p :=
      ((SameArrow.refl s).whiskerRight (word_append A B)).trans
        (whisker_right_right s (V A) (V B)).symm
    have e₂ : V [x] ◁ (σ (A ++ B)).hom ≈ₐ q ≫ₐ r := by
      refine (ih.whiskerLeft rfl).trans ?_
      rw [SameArrow.whiskerLeft_join]
      exact (whisker_left_right (V [x]) a (V B)).symm.join_congr
        (whisker_left_left (V [x]) (V A) b).symm _ _
    have e₃ : (σ (x :: A)).hom ▷ V B ≈ₐ p ≫ₐ q := by
      have e := (crossing_cons x A).whiskerRight (X := V B) rfl
      rw [SameArrow.join_whiskerRight] at e
      exact e
    calc
      _ ≈ₐ (s ▷ V (A ++ B)) ≫ₐ (V [x] ◁ (σ (A ++ B)).hom) := crossing_cons x (A ++ B)
      _ ≈ₐ p ≫ₐ q ≫ₐ r := e₁.join_congr e₂ _ _
      _ ≈ₐ (p ≫ₐ q) ≫ₐ r := .of_eq (SameArrow.join_assoc _ _ _ _ _).symm
      _ ≈ₐ ((σ (x :: A)).hom ▷ V B) ≫ₐ (V (x :: A) ◁ b) :=
        e₃.symm.join_congr ((SameArrow.refl b).whiskerLeft (word_append [x] A).symm) _ _

theorem crossing_append_inv (A B : List G.Obj) :
    (σ (A ++ B)).inv ≈ₐ (V A ◁ (σ B).inv) ≫ₐ ((σ A).inv ▷ V B) :=
  ((crossing_append A B).trans (crossTensor_hom (σ A) (σ B)).symm).inv.trans
    (crossTensor_inv (σ A) (σ B))

end Silmaril.RuntimeWires.Proofs.RuntimeCoherence
