module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Functor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Iteration.Thms

/-! # Coproduct and iteration comparisons of the joined functor -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotationFunctor

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofType sumIso projection_mapIso_sumIso)
open Paper.WithProjectionReturnsAndUnitEta (Step TypeCategory projection denoteFunctor denoteArrow_canonicalIterate)
open Paper.WithProjectionReturnsAndUnitEta.Reification (canonicalIterate)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (Seed)
local notation "Q" => TypeCategory (τ := τ) (Φ := Φ)
local notation "P" => projection (τ := τ) (Φ := Φ)
local notation "F" => Paper.TypeCategory.denoteFunctor (Φ := Φ) J M shared

local notation "G" => denoteFunctor (Φ := Φ) J M shared

theorem factorization : (P) ⋙ (G) = F :=
  CategoryTheory.Quotient.lift_spec _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem preservesFinite : PreservesFiniteCoproducts (G) where
  preserves n := by
    let _ : PreservesFiniteCoproducts ((P) ⋙ (G)) :=
      (factorization (Φ := Φ) J M shared).symm ▸
        Paper.TypeCategory.denoteFunctor_preservesFiniteCoproducts (Φ := Φ) J M shared
    constructor
    intro K
    -- The joined quotient keeps the original objects, so a discrete diagram lifts objectwise.
    let L := Discrete.functor (fun i : Fin n => (K.obj ⟨i⟩).as)
    let liftIso : L ⋙ (P) ≅ K := Discrete.natIso (fun _ => Iso.refl _)
    have preserve : PreservesColimit (L ⋙ (P)) (G) := by
      apply preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (P) (colimit.isColimit L))
      exact isColimitOfPreserves ((P) ⋙ (G)) (colimit.isColimit L)
    exact preservesColimit_of_iso_diagram (G) liftIso

set_option backward.isDefEq.respectTransparency false in
private theorem exactSum (A B : τ) :
    let := preservesFinite (Φ := Φ) J M shared
    (G).map (sumIso (Seed) A B).hom ≫ (PreservesColimitPair.iso (G) (Obj A) (Obj B)).inv =
      (Paper.TypeCategory.denoteExactSumIso J M A B).hom := by
  let := preservesFinite (Φ := Φ) J M shared
  let X := Paper.TypeCategory.ofType (Φ := Φ) A
  let Y := Paper.TypeCategory.ofType (Φ := Φ) B
  let sourceComp := PreservesColimitPair.iso (P) X Y
  let joinedComp := PreservesColimitPair.iso (G) (Obj A) (Obj B)
  let ordinaryComp := Paper.TypeCategory.denoteCoprodIso (Φ := Φ) J M shared A B
  have compares :
      joinedComp ≪≫ (G).mapIso sourceComp = ordinaryComp.symm := by
    apply Iso.ext
    change joinedComp.hom ≫ (G).map sourceComp.hom = ordinaryComp.inv
    rw [← Paper.TypeCategory.denoteFunctor_coprodComparison J M shared A B]
    apply coprod.hom_ext
    · simp only [joinedComp, sourceComp, PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, ← (G).map_comp]
      exact (congrArg (G).map (inl_coprodComparison (P) X Y)).trans (inl_coprodComparison (F) X Y).symm
    · simp only [joinedComp, sourceComp, PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, ← (G).map_comp]
      exact (congrArg (G).map (inr_coprodComparison (P) X Y)).trans (inr_coprodComparison (F) X Y).symm
  have sumOnImage :
      (F).mapIso (Paper.TypeCategory.sumIso A B) =
        (G).mapIso (sumIso (Seed) A B) ≪≫ (G).mapIso sourceComp := by
    change (G).mapIso ((P).mapIso (Paper.TypeCategory.sumIso A B)) = _
    rw [projection_mapIso_sumIso, Functor.mapIso_trans]
  have transport := congrArg Iso.inv compares
  change (G).map sourceComp.inv ≫ joinedComp.inv = ordinaryComp.hom at transport
  have sumHom := congrArg Iso.hom sumOnImage
  change (F).map (Paper.TypeCategory.sumIso A B).hom =
      (G).map (sumIso (Seed) A B).hom ≫ (G).map sourceComp.hom at sumHom
  change (G).map (sumIso (Seed) A B).hom ≫ joinedComp.inv = _
  calc
    _ = ((G).map (sumIso (Seed) A B).hom ≫ (G).map sourceComp.hom) ≫ ordinaryComp.hom := by
      simp only [← transport, Category.assoc, ← (G).map_comp_assoc sourceComp.hom sourceComp.inv,
        Iso.hom_inv_id, (G).map_id, Category.id_comp]
    _ = _ := by
      rw [← sumHom]
      simp only [ordinaryComp, Paper.TypeCategory.denoteCoprodIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_inv, ← (F).map_comp_assoc, Iso.hom_inv_id, (F).map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem mapIterate {A B : τ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    let := preservesFinite (Φ := Φ) J M shared
    (G).map (canonicalIterate f) = CategoryTheory.iterate
      ((G).map f ≫ (PreservesColimitPair.iso (G) (Obj B) (Obj A)).inv) := by
  let := preservesFinite (Φ := Φ) J M shared
  let comparison := PreservesColimitPair.iso (G) (Obj B) (Obj A)
  have changeSum : (G).map (sumIso (Seed) B A).hom ≫ comparison.inv =
      (Paper.TypeCategory.denoteExactSumIso J M B A).hom :=
    exactSum (Φ := Φ) J M shared B A
  have coordinates :
      (G).map (f ≫ (sumIso (Seed) B A).inv) ≫
        (Paper.TypeCategory.denoteExactSumIso J M B A).hom = (G).map f ≫ comparison.inv := by
    rw [← changeSum, ← (G).map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (denoteArrow_canonicalIterate J M shared f).trans (congrArg CategoryTheory.iterate coordinates)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedDenotationFunctor
