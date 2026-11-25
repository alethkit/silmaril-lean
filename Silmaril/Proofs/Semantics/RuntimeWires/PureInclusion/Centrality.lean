module

public import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Naturality
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Whiskering

public section

namespace Silmaril.RuntimeWires.Proofs.PureInclusion

open CategoryTheory MonoidalCategory
open Presentation RuntimeCoherence
open scoped MonoidalCategory PremonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "R" => runtime G
local notation "V" => valueWord (G := G)
local notation "σ" => crossingWord (G := G)

private theorem exchange {X Y U W : Runtime G} (f : X ⟶ Y) (g : U ⟶ W) :
    f ▷ U ≫ Y ◁ g = X ◁ g ≫ f ▷ W :=
  (tensorHom_def f g).symm.trans (tensorHom_def' f g)

/-- Left whiskering a pure arrow cancels the two crossings surrounding it. -/
theorem left_pure (A : Computations G) {X Y : Pure G} (f : X ⟶ Y) :
    (show (A.concat (pureObject X)).boundary ⟶ (A.concat (pureObject Y)).boundary from
      A ◁ (pureInclusion G).map f) ≈ₐ A.boundary ◁ (pureValues G).map f := by
  let p : V X.word ⟶ V Y.word := (pureValues G).map f
  let s := σ A.word
  have he : (s.hom ▷ V X.word) ≫ (V A.word ⊗ R) ◁ p ≫ (s.inv ▷ V Y.word) =
      (R ⊗ V A.word) ◁ p := by
    rw [reassoc_of% (exchange s.hom p), ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
      Category.comp_id]
  refine (left_normal A ((pureInclusion G).map f)).trans (SameArrow.trans ?_ (.of_eq he))
  have h := (SameArrow.refl (s.hom ▷ V X.word)).join_congr
    ((whisker_left_left (V A.word) R p).symm.join_congr
      (SameArrow.refl (s.inv ▷ V Y.word)) (by runtime_word) rfl) (by runtime_word) rfl
  refine h.trans (.of_eq ?_)
  rw [SameArrow.join_eq, SameArrow.join_eq]

private theorem move_inv {X Y : Pure G} (f : X ⟶ Y) :
    (pureValues G).map f ▷ R ≫ (σ Y.word).inv =
      (σ X.word).inv ≫ R ◁ (pureValues G).map f := by
  let p : V X.word ⟶ V Y.word := (pureValues G).map f
  change p ▷ R ≫ (σ Y.word).inv = (σ X.word).inv ≫ R ◁ p
  have hf : (σ X.word).hom ≫ p ▷ R = R ◁ p ≫ (σ Y.word).hom := pureValues_natural f
  apply (cancel_epi (σ X.word).hom).1
  rw [← Category.assoc, hf, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem central_right {X Y : Pure G} (f : X ⟶ Y)
    {A B : Computations G} (g : A ⟶ B) :
    g ⋉ (pureInclusion G).map f = g ⋊ (pureInclusion G).map f := by
  let p : V X.word ⟶ V Y.word := (pureValues G).map f
  let q : A.boundary ⟶ B.boundary := g
  exact ((SameArrow.comp (right_normal g (pureObject X)) (left_pure B f)).trans
    ((SameArrow.of_eq (exchange q p)).trans
      (SameArrow.comp (left_pure A f).symm (right_normal g (pureObject Y)).symm))).eq

private theorem central_left {X Y : Pure G} (f : X ⟶ Y)
    {A B : Computations G} (g : A ⟶ B) :
    (pureInclusion G).map f ⋉ g = (pureInclusion G).map f ⋊ g := by
  let p : V X.word ⟶ V Y.word := (pureValues G).map f
  let a := V A.word
  let b := V B.word
  let q : R ⊗ a ⟶ R ⊗ b := g
  let s := σ X.word
  let t := σ Y.word
  have ha : ((R ◁ p) ▷ a) ≫ₐ (t.hom ▷ a) = (s.hom ▷ a) ≫ₐ ((p ▷ R) ▷ a) := by
    have hf : R ◁ p ≫ t.hom = s.hom ≫ p ▷ R := (pureValues_natural f).symm
    rw [SameArrow.join_eq, SameArrow.join_eq, ← comp_whiskerRight, ← comp_whiskerRight, hf]
  have hb : (s.inv ▷ b) ≫ₐ ((R ◁ p) ▷ b) = ((p ▷ R) ▷ b) ≫ₐ (t.inv ▷ b) := by
    have hf : s.inv ≫ R ◁ p = p ▷ R ≫ t.inv := (move_inv f).symm
    rw [SameArrow.join_eq, SameArrow.join_eq, ← comp_whiskerRight, ← comp_whiskerRight, hf]
  have hn : ((p ▷ R) ▷ a) ≫ₐ (V Y.word ◁ q) ≈ₐ (V X.word ◁ q) ≫ₐ ((p ▷ R) ▷ b) := by
    have l := (whisker_right_right p R a).join_congr
      (SameArrow.refl (V Y.word ◁ q)) (by runtime_word) rfl
    have r := (SameArrow.refl (V X.word ◁ q)).join_congr
      (whisker_right_right p R b) (by runtime_word) rfl
    exact l.trans ((SameArrow.of_eq (by
      rw [SameArrow.join_eq, SameArrow.join_eq]
      exact exchange p q)).trans r.symm)
  have hl := (right_normal ((pureInclusion G).map f) A).comp_join (left_normal (pureObject Y) g)
    (by runtime_word)
  have hr := (left_normal (pureObject X) g).comp_join (right_normal ((pureInclusion G).map f) B)
    (by runtime_word)
  let lhs : pureObject X ⊗ A ⟶ pureObject Y ⊗ B := (pureInclusion G).map f ⋉ g
  let rhs : pureObject X ⊗ A ⟶ pureObject Y ⊗ B := (pureInclusion G).map f ⋊ g
  change (show ((pureObject X).concat A).boundary ⟶ ((pureObject Y).concat B).boundary from
    lhs) = rhs
  apply SameArrow.eq
  refine hl.trans (SameArrow.trans ?_ hr.symm)
  change ((R ◁ p) ▷ a) ≫ₐ (t.hom ▷ a) ≫ₐ (V Y.word ◁ q) ≫ₐ (t.inv ▷ b) ≈ₐ
    ((s.hom ▷ a) ≫ₐ (V X.word ◁ q) ≫ₐ (s.inv ▷ b)) ≫ₐ ((R ◁ p) ▷ b)
  calc
    _ ≈ₐ (((R ◁ p) ▷ a) ≫ₐ (t.hom ▷ a)) ≫ₐ (V Y.word ◁ q) ≫ₐ (t.inv ▷ b) :=
      .of_eq (SameArrow.join_assoc _ _ _ _ _).symm
    _ ≈ₐ ((s.hom ▷ a) ≫ₐ ((p ▷ R) ▷ a)) ≫ₐ (V Y.word ◁ q) ≫ₐ (t.inv ▷ b) :=
      (SameArrow.of_eq ha).join_congr (.refl _) _ _
    _ ≈ₐ (s.hom ▷ a) ≫ₐ (((p ▷ R) ▷ a) ≫ₐ (V Y.word ◁ q)) ≫ₐ (t.inv ▷ b) :=
      .of_eq (by simp only [SameArrow.join_assoc])
    _ ≈ₐ (s.hom ▷ a) ≫ₐ ((V X.word ◁ q) ≫ₐ ((p ▷ R) ▷ b)) ≫ₐ (t.inv ▷ b) :=
      (SameArrow.refl _).join_congr (hn.join_congr (.refl _) _ _) _ _
    _ ≈ₐ ((s.hom ▷ a) ≫ₐ (V X.word ◁ q) ≫ₐ (s.inv ▷ b)) ≫ₐ ((R ◁ p) ▷ b) :=
      .of_eq (by simp only [SameArrow.join_assoc, hb])

theorem image_central {X Y : Pure G} (f : X ⟶ Y) :
    PremonoidalCategory.IsCentral ((pureInclusion G).map f) :=
  ⟨central_left f, central_right f⟩

end Silmaril.RuntimeWires.Proofs.PureInclusion
