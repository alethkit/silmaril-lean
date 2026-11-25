module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect

/-! # Outward postcomposition through a contextual dispatcher -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (mapDispatcherExit)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop retainLeft splitMapCoprod)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
open CategoryTheory.CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Distributor

variable (J : V ⥤ C) [DistributiveFreydCategory J]

private noncomputable def route (E A S : V) :
    J.obj (E ⊗ (A ⨿ S)) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ S) :=
  J.map (DistributiveTensor.leftIso E A S).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ S)

private instance route_isIso (E A S : V) : IsIso (route J E A S) := by
  unfold route splitMapCoprod
  infer_instance

@[reassoc] private theorem route_inl (E A S : V) :
    J.map (E ◁ (coprod.inl : A ⟶ A ⨿ S)) ≫ route J E A S = coprod.inl :=
  distributeMap_inl J E A S

@[reassoc] private theorem route_inr (E A S : V) :
    J.map (E ◁ (coprod.inr : S ⟶ A ⨿ S)) ≫ route J E A S = coprod.inr :=
  distributeMap_inr J E A S

@[reassoc] private theorem inl_route_inv (E A S : V) :
    coprod.inl ≫ inv (route J E A S) = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ S)) := by
  rw [← route_inl J E A S, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

@[reassoc] private theorem inr_route_inv (E A S : V) :
    coprod.inr ≫ inv (route J E A S) = J.map (E ◁ (coprod.inr : S ⟶ A ⨿ S)) := by
  rw [← route_inr J E A S, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

@[reassoc] private theorem mapDispatcherExit_inl {A B S : V} (k : J.obj A ⟶ J.obj B) :
    J.map (coprod.inl : A ⟶ A ⨿ S) ≫ mapDispatcherExit J k =
      k ≫ J.map (coprod.inl : B ⟶ B ⨿ S) := by
  simp only [mapDispatcherExit, map_inl_inv_coprodComparison_assoc, splitMapCoprod, coprod.inl_desc]

@[reassoc] private theorem mapDispatcherExit_inr {A B S : V} (k : J.obj A ⟶ J.obj B) :
    J.map (coprod.inr : S ⟶ A ⨿ S) ≫ mapDispatcherExit J k =
      J.map (coprod.inr : S ⟶ B ⨿ S) := by
  simp only [mapDispatcherExit, map_inr_inv_coprodComparison_assoc, splitMapCoprod, coprod.inr_desc]

@[reassoc] private theorem retainLeft_mapDispatcherExit {E A B S : V} (k : J.obj A ⟶ J.obj B) :
    retainLeft J (R := E) (mapDispatcherExit (S := S) J k) ≫ route J E B S =
      route J E A S ≫ coprod.map (retainLeft J (R := E) k) (𝟙 (J.obj (E ⊗ S))) := by
  apply (cancel_epi (inv (route J E A S))).mp
  rw [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · rw [inl_route_inv_assoc, ← retainLeft_map, ← Category.assoc, ← retainLeft_comp,
      mapDispatcherExit_inl,
      retainLeft_comp, retainLeft_map, Category.assoc, route_inl, coprod.inl_map]
  · rw [inr_route_inv_assoc, ← retainLeft_map, ← Category.assoc, ← retainLeft_comp,
      mapDispatcherExit_inr,
      retainLeft_map, route_inr, coprod.inr_map, Category.id_comp]

end Distributor

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem contextualLoop_mapExit {E A B S : V}
    (body : J.obj (E ⊗ S) ⟶ J.obj (A ⨿ S)) (k : J.obj A ⟶ J.obj B) :
    contextualLoop J (body ≫ mapDispatcherExit J k) = contextualLoop J body ≫ k := by
  let keep : E ⊗ S ⟶ E ⊗ (E ⊗ S) :=
    CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst E S) (𝟙 _)
  let step := J.map keep ≫ retainLeft J (R := E) body ≫ route J E A S
  change iterate (J.map keep ≫ retainLeft J (R := E) (body ≫ mapDispatcherExit J k) ≫
    route J E B S) ≫ J.map (snd E B) = (iterate step ≫ J.map (snd E A)) ≫ k
  rw [retainLeft_comp, Category.assoc, retainLeft_mapDispatcherExit]
  have hstep : iterate (step ≫ coprod.map (retainLeft J k) (𝟙 _)) =
      iterate step ≫ retainLeft J k := (ElgotCategory.naturality step _).symm
  simp only [step, Category.assoc] at hstep
  rw [hstep, Category.assoc,
    retainLeft_snd J (FreydCategory.CentralUnit.unit_central (J := J)), Category.assoc]

theorem caseWithContext_mapExit {E A B S : V}
    (entry : J.obj E ⟶ J.obj (A ⨿ S))
    (loop : J.obj (E ⊗ S) ⟶ J.obj A) (k : J.obj A ⟶ J.obj B) :
    caseWithContext J (entry ≫ mapDispatcherExit J k) (J.map (snd E B)) (loop ≫ k) =
      caseWithContext J entry (J.map (snd E A)) loop ≫ k := by
  unfold caseWithContext
  rw [← Category.assoc (J.map (DistributiveTensor.leftIso E B S).inv),
    ← Category.assoc (J.map (DistributiveTensor.leftIso E A S).inv)]
  change bindArrow J (entry ≫ mapDispatcherExit J k)
      (route J E B S ≫ coprod.desc (J.map (snd E B)) (loop ≫ k)) =
    bindArrow J entry (route J E A S ≫ coprod.desc (J.map (snd E A)) loop) ≫ k
  dsimp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind]
  simp only [extend_eq_retainLeft, retainLeft_comp, Category.assoc,
    retainLeft_mapDispatcherExit_assoc]
  congr 3
  apply coprod.hom_ext
  · rw [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc]
    exact retainLeft_snd J (FreydCategory.CentralUnit.unit_central (J := J)) k
  · simp

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
