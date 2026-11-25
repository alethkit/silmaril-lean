module

public import Silmaril.Semantics.RuntimeWires.Coherence.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Crossing

public section

namespace Silmaril.RuntimeWires.Proofs.RuntimeCoherence

open CategoryTheory MonoidalCategory
open Presentation
open scoped SameArrow RuntimeCoherence MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "R" => runtime G
local notation "V" => valueWord (G := G)
local notation "σ" => crossingWord (G := G)
local notation "A₀" => Computations.empty (G := G)

theorem splitRight_hom (A B : Computations G) :
    (A.splitRight B).hom = eqToHom
      (show (A.concat B).boundary = A.boundary ⊗ V B.word from
        (congrArg (R ⊗ ·) (word_append A.word B.word)).trans
          (Diagram.Presented.concat_assoc R (V A.word) (V B.word)).symm) :=
  eqToHom_trans (congrArg (R ⊗ ·) (word_append A.word B.word))
    (Diagram.Presented.concat_assoc R (V A.word) (V B.word)).symm

theorem splitRight_inv (A B : Computations G) :
    (A.splitRight B).inv = eqToHom
      (show A.boundary ⊗ V B.word = (A.concat B).boundary from
        (Diagram.Presented.concat_assoc R (V A.word) (V B.word)).trans
          (congrArg (R ⊗ ·) (word_append A.word B.word)).symm) :=
  eqToHom_trans (Diagram.Presented.concat_assoc R (V A.word) (V B.word))
    (congrArg (R ⊗ ·) (word_append A.word B.word)).symm

theorem splitLeft_hom (A B : Computations G) :
    (A.splitLeft B).hom ≈ₐ (σ A.word).hom ▷ V B.word := by
  change (A.splitRight B).hom ≫
    (((σ A.word).hom ⊗ₘ 𝟙 (V B.word)) ≫ (α_ (V A.word) R (V B.word)).hom) ≈ₐ _
  have e := (SameArrow.of_eq (splitRight_hom A B)).comp
    ((SameArrow.of_eq (tensorHom_id (σ A.word).hom (V B.word))).comp
      (.of_eq (assoc_hom_eq (V A.word) R (V B.word))))
  exact e.trans ((SameArrow.cast_comp _).trans (SameArrow.comp_cast _))

theorem splitLeft_inv (A B : Computations G) :
    (A.splitLeft B).inv ≈ₐ (σ A.word).inv ▷ V B.word := by
  change ((α_ (V A.word) R (V B.word)).inv ≫ ((σ A.word).inv ⊗ₘ 𝟙 (V B.word))) ≫
    (A.splitRight B).inv ≈ₐ _
  refine (SameArrow.of_eq (Category.assoc (α_ (V A.word) R (V B.word)).inv
    ((σ A.word).inv ⊗ₘ 𝟙 (V B.word)) (A.splitRight B).inv)).trans ?_
  have e := (SameArrow.of_eq (assoc_inv_eq (V A.word) R (V B.word))).comp
    ((SameArrow.of_eq (tensorHom_id (σ A.word).inv (V B.word))).comp
      (.of_eq (splitRight_inv A B)))
  exact e.trans ((SameArrow.cast_comp _).trans (SameArrow.comp_cast _))

theorem right_normal {A B : Computations G} (f : A ⟶ B) (C : Computations G) :
    (show (A.concat C).boundary ⟶ (B.concat C).boundary from f ▷ C) ≈ₐ
      (show A.boundary ⟶ B.boundary from f) ▷ V C.word := by
  change (A.splitRight C).hom ≫ (show A.boundary ⟶ B.boundary from f) ▷ V C.word ≫
    (B.splitRight C).inv ≈ₐ _
  rw [splitRight_hom, splitRight_inv]
  exact (SameArrow.cast_comp _).trans (SameArrow.comp_cast _)

theorem left_normal {B C : Computations G} (A : Computations G) (f : B ⟶ C) :
    (show (A.concat B).boundary ⟶ (A.concat C).boundary from A ◁ f) ≈ₐ
      ((σ A.word).hom ▷ V B.word) ≫ₐ
        (V A.word ◁ (show B.boundary ⟶ C.boundary from f)) ≫ₐ
        ((σ A.word).inv ▷ V C.word) := by
  change (A.splitLeft B).hom ≫ V A.word ◁ (show B.boundary ⟶ C.boundary from f) ≫
    (A.splitLeft C).inv ≈ₐ _
  exact (splitLeft_hom A B).comp_join
    ((SameArrow.refl _).comp_join (splitLeft_inv A C) (by runtime_word)) (by runtime_word)

theorem right_unit {A B : Computations G} (f : A ⟶ B) :
    (show (A.concat A₀).boundary ⟶ (B.concat A₀).boundary from f ▷ A₀) ≈ₐ
      (show A.boundary ⟶ B.boundary from f) :=
  (right_normal f A₀).trans (whiskerRight_unit _)

theorem left_unit {A B : Computations G} (f : A ⟶ B) :
    (show (Computations.concat A₀ A).boundary ⟶ (Computations.concat A₀ B).boundary from A₀ ◁ f) ≈ₐ
      (show A.boundary ⟶ B.boundary from f) := by
  let p : A.boundary ⟶ B.boundary := f
  calc
    _ ≈ₐ (𝟙 R ▷ V A.word) ≫ₐ p ≫ₐ (𝟙 R ▷ V B.word) :=
      (left_normal A₀ f).trans ((crossing_nil.whiskerRight rfl).join_congr
        ((whiskerLeft_unit p).join_congr (crossing_nil_inv.whiskerRight rfl) _ _) _ _)
    _ ≈ₐ p := by
      simp only [id_whiskerRight]
      exact (SameArrow.id_join _).trans (SameArrow.join_id _)

theorem right_right {A B : Computations G} (f : A ⟶ B) (C D : Computations G) :
    (show ((A.concat C).concat D).boundary ⟶ ((B.concat C).concat D).boundary from
      (f ▷ C) ▷ D) ≈ₐ
    (show (A.concat (C.concat D)).boundary ⟶ (B.concat (C.concat D)).boundary from
      f ▷ (C.concat D)) := by
  let p : A.boundary ⟶ B.boundary := f
  calc
    _ ≈ₐ (p ▷ V C.word) ▷ V D.word :=
      (right_normal (f ▷ C) D).trans ((right_normal f C).whiskerRight rfl)
    _ ≈ₐ p ▷ (V C.word ⊗ V D.word) := whisker_right_right p _ _
    _ ≈ₐ p ▷ V (C.word ++ D.word) := (SameArrow.refl p).whiskerRight (word_append ..).symm
    _ ≈ₐ _ := (right_normal f (C.concat D)).symm

theorem left_right (A : Computations G) {B C : Computations G} (f : B ⟶ C)
    (D : Computations G) :
    (show ((A.concat B).concat D).boundary ⟶ ((A.concat C).concat D).boundary from
      (A ◁ f) ▷ D) ≈ₐ
    (show (A.concat (B.concat D)).boundary ⟶ (A.concat (C.concat D)).boundary from
      A ◁ (f ▷ D)) := by
  let p : B.boundary ⟶ C.boundary := f
  let s := (σ A.word).hom
  let t := (σ A.word).inv
  have h := (left_normal A f).whiskerRight (X := V D.word) rfl
  simp only [SameArrow.join_whiskerRight] at h
  refine (right_normal (A ◁ f) D).trans (h.trans ?_)
  refine SameArrow.trans ?_ (left_normal A (f ▷ D)).symm
  have hs := (whisker_right_right s (V B.word) (V D.word)).trans
    ((SameArrow.refl s).whiskerRight (word_append B.word D.word).symm)
  have ht := (whisker_right_right t (V C.word) (V D.word)).trans
    ((SameArrow.refl t).whiskerRight (word_append C.word D.word).symm)
  have hp := (whisker_left_right (V A.word) p (V D.word)).trans
    ((right_normal f D).symm.whiskerLeft (X := V A.word) rfl)
  exact hs.join_congr (hp.join_congr ht _ _) _ _

theorem left_left (A B : Computations G) {C D : Computations G} (f : C ⟶ D) :
    (show ((A.concat B).concat C).boundary ⟶ ((A.concat B).concat D).boundary from
      (A.concat B) ◁ f) ≈ₐ
    (show (A.concat (B.concat C)).boundary ⟶ (A.concat (B.concat D)).boundary from
      A ◁ (B ◁ f)) := by
  let p : C.boundary ⟶ D.boundary := f
  let a := V A.word
  let b := V B.word
  let c := V C.word
  let d := V D.word
  let x := σ A.word
  let y := σ B.word
  have hl := (crossing_append A.word B.word).whiskerRight (X := c) rfl
  have hr := (crossing_append_inv A.word B.word).whiskerRight (X := d) rfl
  simp only [SameArrow.join_whiskerRight] at hl hr
  have hm := (SameArrow.refl p).whiskerLeft (word_append A.word B.word)
  have h₁ := (left_normal (A.concat B) f).trans (hl.join_congr (hm.join_congr hr (by runtime_word) (by runtime_word))
    (by runtime_word) (by runtime_word))
  simp only [SameArrow.join_assoc] at h₁
  have hm' := (left_normal B f).whiskerLeft (X := a) rfl
  simp only [SameArrow.whiskerLeft_join] at hm'
  have hl' := ((SameArrow.refl x.hom).whiskerRight (word_append B.word C.word)).trans
    (whisker_right_right x.hom b c).symm
  have hr' := ((SameArrow.refl x.inv).whiskerRight (word_append B.word D.word)).trans
    (whisker_right_right x.inv b d).symm
  have h₂ := (left_normal A (B ◁ f)).trans (hl'.join_congr (hm'.join_congr hr' (by runtime_word) (by runtime_word))
    (by runtime_word) (by runtime_word))
  simp only [SameArrow.join_assoc] at h₂
  refine h₁.trans (SameArrow.trans ?_ h₂.symm)
  exact (SameArrow.refl _).join_congr
    ((whisker_left_right a y.hom c).join_congr
      ((whisker_left_left a b p).join_congr
        ((whisker_left_right a y.inv d).join_congr (.refl _) _ _) _ _) _ _) _ _

end Silmaril.RuntimeWires.Proofs.RuntimeCoherence
