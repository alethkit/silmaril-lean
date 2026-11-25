module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs
import Silmaril.Proofs.Semantics.Calco2019.CompleteElgot.Dinaturality
import Silmaril.Proofs.Semantics.Calco2019.CompleteElgot.Types

/-! # Complete Elgot laws as CALCO laws -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

/-- In a Kleisli category with total guards, dinaturality follows from the fixpoint,
codiagonal and pure uniformity equations. This is the total Kleisli case of Proposition 17. -/
theorem dinaturality_of_uniform {C : Type u} [Category.{v} C] {P : Coproducts C}
    {T : Monad C} (F : (Guardedness.greatest (P.kleisli T)).Fixpoints)
    (laws : F.NaturalCodiagonal) (uniform : F.Uniform (Kleisli.Adjunction.toKleisli T)) :
    F.Dinaturality :=
  Proofs.dinaturality_of_uniform F laws uniform

section Categories

variable {K : Type u} [Category.{v} K] [HasFiniteCoproducts K]
  [Iteration K] [ElgotCategory K]

omit [Iteration K] [ElgotCategory K] in
private theorem selected_map {A B D E : K} (f : A ⟶ D) (g : B ⟶ E) :
    (Coproducts.ofHasBinaryCoproducts K).map f g = coprod.map f g := by
  rw [Coproducts.map, Coproducts.selected_desc]
  change coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr) = coprod.map f g
  apply coprod.hom_ext <;> simp

/-- The three equations of the categorical interface agree with their CALCO forms
on the same selected coproducts. -/
theorem categorical_naturalCodiagonal : (categoricalFixpoints K).NaturalCodiagonal where
  naturality {X Y Z} f g _ _ := by
    change CategoryTheory.iterate (f ≫ (Coproducts.ofHasBinaryCoproducts K).map g (𝟙 X)) =
      CategoryTheory.iterate f ≫ g
    rw [selected_map]
    exact (ElgotCategory.naturality f g).symm
  codiagonal {X Y} f _ _ _ _ := by
    change CategoryTheory.iterate (f ≫ (Coproducts.ofHasBinaryCoproducts K).merge) =
      CategoryTheory.iterate (CategoryTheory.iterate f)
    rw [Coproducts.merge, Coproducts.selected_desc]
    exact (ElgotCategory.codiagonal f).symm

/-- The two presentations of the uniformity square permit precisely the same maps
of states, namely the arrows in the image of the given functor. -/
theorem categorical_uniform_iff {V : Type*} [Category* V] (J : V ⥤ K) :
    (categoricalFixpoints K).Uniform J ↔
      ∀ {A D : V} {B : K} (f : J.obj A ⟶ B ⨿ J.obj A) (g : J.obj D ⟶ B ⨿ J.obj D)
        (h : A ⟶ D), f ≫ coprod.map (𝟙 B) (J.map h) = J.map h ≫ g →
          CategoryTheory.iterate f = J.map h ≫ CategoryTheory.iterate g := by
  constructor
  · intro uniform A D B f g h comm
    exact (uniform g f h trivial trivial (by rw [selected_map]; exact comm.symm)).symm
  · intro uniform D A B g f h _ _ comm
    exact (uniform f g h (by rw [selected_map] at comm; exact comm.symm)).symm

end Categories

section Types

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]
  [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]

theorem type_fixpoint (X Y : Kleisli (ofTypeMonad m))
    (f : X ⟶ (typeCoproducts.kleisli (ofTypeMonad m)).sum Y X) :
    Guardedness.IsFixpoint (P := typeCoproducts.kleisli (ofTypeMonad m))
      f (computation m (Elgot.iter f.of)) :=
  Proofs.fixpoint m X Y f

/-- The CALCO solutions are the original monadic iteration, with the inherited coproduct. -/
@[expose] noncomputable def typeFixpoints :
    (Guardedness.greatest (typeCoproducts.kleisli (ofTypeMonad m))).Fixpoints where
  iterate f _ := computation m (Elgot.iter f.of)
  fixpoint {X Y} f _ := type_fixpoint m X Y f

theorem type_naturalCodiagonal : (typeFixpoints m).NaturalCodiagonal where
  naturality {X Y Z} f g _ _ := Proofs.naturality m X Y Z f g
  codiagonal {X Y} f _ _ _ _ := Proofs.codiagonal m X Y f

theorem type_uniformity :
    (typeFixpoints m).Uniform (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) :=
  fun f g h _ _ comm => Proofs.uniformity m f g h comm

/-- A lawful Silmaril type monad is a CALCO Elgot monad with total guardedness. -/
@[expose] noncomputable def ofLawfulMonad : GuardedElgotMonad typeCoproducts where
  monad := ofTypeMonad m
  guard := Guardedness.greatest _
  iteration := {
    toFixpoints := typeFixpoints m
    naturalCodiagonal := type_naturalCodiagonal m
    dinaturality := dinaturality_of_uniform (typeFixpoints m)
      (type_naturalCodiagonal m) (type_uniformity m) }
  uniformity := type_uniformity m

theorem ofLawfulMonad_isElgot : (ofLawfulMonad m).IsElgot := fun _ => trivial

/-- Transport a body from the selected coproduct of the existing Kleisli
semantics to CALCO's inherited sum. The iterations give the same arrow. -/
theorem kleisli_iterate_eq {X Y : Kleisli (ofTypeMonad m)} (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate f =
      (ofLawfulMonad m).iteration.iterate (f ≫ (Kleisli.Type.coprodIsoSum m Y X).hom) trivial :=
  rfl

/-- The existing categorical iteration agrees with CALCO's chosen solution
after comparison of the two coproduct cocones. -/
theorem selected_iterate_eq (X Y : Type u) (f : X → m (Y ⊕ X)) :
    CategoryTheory.iterate (computation m f ≫ sumToSelected m Y X) =
      (ofLawfulMonad m).iteration.iterate (computation m f) trivial :=
  Proofs.selected_iterate m X Y f

end Types

/-- Total guard and unique fixpoints are distinct conditions, even for the
repository's lawful partiality semantics. A pure self-loop has several fixpoints. -/
theorem part_not_iterative :
    ¬ (Guardedness.greatest (typeCoproducts.kleisli (ofTypeMonad Part.{u}))).Iterative :=
  Proofs.part_not_iterative

end Silmaril.Calco2019
