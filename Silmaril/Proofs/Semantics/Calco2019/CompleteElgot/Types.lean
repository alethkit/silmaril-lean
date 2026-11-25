module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs

@[expose] public section

universe u

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

local notation "T" => ofTypeMonad m
local notation "Q" => typeCoproducts.kleisli T
local notation "J" => Kleisli.Adjunction.toKleisli T

private theorem pure_comp {X Y Z : Type u} (f : X → Y) (g : Y → m Z) :
    (J).map (↾f) ≫ computation m g = computation m (g ∘ f) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  funext x
  exact pure_bind (f x) g

private theorem comp_computation {X Y Z : Type u} (f : X → m Y) (g : Y → m Z) :
    computation m f ≫ computation m g = computation m (f >=> g) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  exact Kleisli.Type.comp_of_eq_kleisliRight m _ _

private theorem desc_computation {X Y Z : Type u} (f : X → m Z) (g : Y → m Z) :
    (Q).desc (computation m f) (computation m g) = computation m (Sum.elim f g) := by
  apply (Q).hom_ext
  · rw [(Q).inl_desc]
    exact (pure_comp m Sum.inl (Sum.elim f g)).symm
  · rw [(Q).inr_desc]
    exact (pure_comp m Sum.inr (Sum.elim f g)).symm

private theorem map_return {X Y Z : Type u} (g : Y → m Z) :
    (Q).map (computation m g) (𝟙 ((J).obj X)) =
      computation m (Sum.elim (g >=> Elgot.liftPure Sum.inl) (Elgot.liftPure Sum.inr)) := by
  rw [Coproducts.map, Category.id_comp]
  change (Q).desc (computation m g ≫ computation m (Elgot.liftPure Sum.inl))
    (computation m (Elgot.liftPure Sum.inr)) = _
  rw [comp_computation, desc_computation]

private theorem merge_computation (X Y : Type u) :
    ((Q).merge : (Q).sum ((Q).sum ((J).obj Y) ((J).obj X)) ((J).obj X) ⟶ (Q).sum ((J).obj Y) ((J).obj X)) =
      computation m (Elgot.liftPure Elgot.flatten) := by
  apply (Q).hom_ext
  · rw [Coproducts.merge, (Q).inl_desc]
    exact (pure_comp m Sum.inl (Elgot.liftPure Elgot.flatten)).symm
  · rw [Coproducts.merge, (Q).inr_desc]
    exact (pure_comp m Sum.inr (Elgot.liftPure Elgot.flatten)).symm

private theorem map_state {X Z Y : Type u} (h : Z → X) :
    (Q).map (𝟙 ((J).obj Y)) ((J).map (↾h)) = computation m (Elgot.liftPure (Sum.map id h)) := by
  apply (Q).hom_ext
  · rw [Coproducts.map, (Q).inl_desc, Category.id_comp]
    exact (pure_comp m Sum.inl (Elgot.liftPure (Sum.map id h))).symm
  · rw [Coproducts.map, (Q).inr_desc]
    change (J).map (↾h) ≫ computation m (Elgot.liftPure Sum.inr) =
      (J).map (↾(Sum.inr : Z → Y ⊕ Z)) ≫ computation m (Elgot.liftPure (Sum.map id h))
    exact (pure_comp m h (Elgot.liftPure Sum.inr)).trans
      (pure_comp m Sum.inr (Elgot.liftPure (Sum.map id h))).symm

variable [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]

theorem fixpoint (X Y : Kleisli T) (f : X ⟶ (Q).sum Y X) :
    f ≫ (Q).desc (𝟙 Y) (computation m (Elgot.iter f.of)) =
      computation m (Elgot.iter f.of) := by
  cases X
  cases Y
  change computation m f.of ≫ (Q).desc (computation m pure)
    (computation m (Elgot.iter f.of)) = _
  rw [desc_computation, comp_computation]
  exact congrArg (computation m) (Elgot.LawfulElgotMonad.fixpoint (m := m) f.of).symm

theorem naturality (X Y Z : Kleisli T) (f : X ⟶ (Q).sum Y X) (g : Y ⟶ Z) :
    computation m (Elgot.iter (f ≫ (Q).map g (𝟙 X)).of) =
      computation m (Elgot.iter f.of) ≫ g := by
  obtain ⟨A⟩ := X
  obtain ⟨B⟩ := Y
  obtain ⟨C⟩ := Z
  let body : A → m (B ⊕ A) := f.of
  let after : B → m C := g.of
  change computation m (Elgot.iter (computation m body ≫
    (Q).map (computation m after) (𝟙 ((J).obj A))).of) =
    computation m (Elgot.iter body) ≫ computation m after
  rw [map_return m (X := A) after, comp_computation, comp_computation]
  exact congrArg (computation m) (Elgot.LawfulElgotMonad.naturality (m := m) f.of g.of).symm

theorem codiagonal (X Y : Kleisli T) (f : X ⟶ (Q).sum ((Q).sum Y X) X) :
    computation m (Elgot.iter (f ≫ (Q).merge).of) =
      computation m (Elgot.iter (Elgot.iter f.of)) := by
  cases X
  cases Y
  change computation m (Elgot.iter (computation m f.of ≫ (Q).merge).of) = _
  rw [merge_computation, comp_computation]
  exact congrArg (computation m) (Elgot.LawfulElgotMonad.codiagonal (m := m) f.of).symm

theorem uniformity {X Z : Type u} {Y : Kleisli T}
    (f : (J).obj X ⟶ (Q).sum Y ((J).obj X)) (g : (J).obj Z ⟶ (Q).sum Y ((J).obj Z)) (h : Z ⟶ X)
    (comm : (J).map h ≫ f = g ≫ (Q).map (𝟙 Y) ((J).map h)) :
    (J).map h ≫ computation m (Elgot.iter f.of) = computation m (Elgot.iter g.of) := by
  obtain ⟨B⟩ := Y
  let f' : X → m (B ⊕ X) := f.of
  let g' : Z → m (B ⊕ Z) := g.of
  change (J).map (↾(⇑h)) ≫ computation m f' =
    computation m g' ≫ (Q).map (𝟙 ((J).obj B)) ((J).map (↾(⇑h))) at comm
  rw [map_state m (Y := B) h, pure_comp, comp_computation] at comm
  have comm' := congrArg (fun q : (J).obj Z ⟶ (J).obj (B ⊕ X) => ⇑q.of) comm.symm
  have law := Elgot.LawfulElgotMonad.uniformity (m := m) g' f' h (by
    funext z
    change (g' z >>= Elgot.liftPure (Sum.map id h)) = (pure (h z) >>= f')
    rw [pure_bind]
    exact congrFun comm' z)
  change (J).map (↾(⇑h)) ≫ computation m (Elgot.iter f') = computation m (Elgot.iter g')
  rw [pure_comp]
  apply congrArg (computation m)
  funext z
  have hz := congrFun law.symm z
  change (pure (h z) >>= Elgot.iter f') = Elgot.iter g' z at hz
  rw [pure_bind] at hz
  exact hz

omit [Elgot.LawfulElgotMonad m] in
theorem selected_iterate (X Y : Type u) (f : X → m (Y ⊕ X)) :
    CategoryTheory.iterate (computation m f ≫ sumToSelected m Y X) =
      computation m (Elgot.iter f) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  rw [Kleisli.Type.iterate_of]
  simp [sumToSelected]

/-- Pure self-loops have multiple fixpoints in the partiality monad. -/
theorem part_not_iterative :
    ¬ (Guardedness.greatest (typeCoproducts.kleisli (ofTypeMonad Part.{u}))).Iterative := by
  let loop := computation Part (fun x : PUnit.{u + 1} => pure (Sum.inr x : PUnit.{u + 1} ⊕ PUnit.{u + 1}))
  let constant (p : Part PUnit.{u + 1}) := computation Part (fun _ : PUnit.{u + 1} => p)
  have fixed (p : Part PUnit.{u + 1}) :
      Guardedness.IsFixpoint (P := typeCoproducts.kleisli (ofTypeMonad Part.{u})) loop (constant p) := by
    change loop ≫ (typeCoproducts.kleisli (ofTypeMonad Part.{u})).desc
      (computation Part pure) (constant p) = constant p
    dsimp only [loop, constant]
    rw [desc_computation, comp_computation]
    apply congrArg (computation Part)
    funext a
    exact pure_bind (Sum.inr a) _
  intro iterative
  obtain ⟨f, _, unique⟩ := iterative loop trivial
  have eq := (unique (constant Part.none) (fixed Part.none)).trans
    (unique (constant (Part.some PUnit.unit)) (fixed (Part.some PUnit.unit))).symm
  exact Part.none_ne_some PUnit.unit (congrArg (fun g => g.of PUnit.unit) eq)

end Silmaril.Calco2019.Proofs
