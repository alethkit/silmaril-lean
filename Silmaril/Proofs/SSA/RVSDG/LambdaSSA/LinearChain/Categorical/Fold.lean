module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Context
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatch
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Iteration

/-! # Categorical equality of the linear dispatcher and γ/θ lowering -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (RegionDenotes labelObj labelInject labelObjToFinite labelAppendSplit
    labelAppendSplit_local labelAppendSplit_exit labelObjToFinite_local)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
variable (M : TypeModel τ V) [InstructionModel J M Φ]
variable {A B E D : τ} {tail : List τ}

omit [InstructionModel J M Φ] in
@[reassoc] private theorem at_local {n : Nat} (R : Fin n → τ) {T : C}
    (arrows : ∀ i, J.obj (M.obj (R i)) ⟶ T) (i : Fin n) :
    J.map (localInject M R i) ≫ (J.map (labelObjToFinite M R) ≫ dispatch J M R arrows) =
      arrows i := by
  rw [← J.map_comp_assoc, localInject, labelObjToFinite_local, dispatch_at]

private theorem routes_of_legs {I O : C} (f : I ⟶ O ⨿ I)
    (exit : J.obj (M.obj D) ⟶ O) (back : J.obj (M.obj A) ⟶ O)
    (b : Body Φ A D B tail)
    (entries : ∀ i : Fin (B :: tail).length, J.obj (M.obj ((B :: tail).get i)) ⟶ I)
    (legs : ∀ i, entries i ≫ f =
      bodyArrows J M (exit ≫ coprod.inl) (back ≫ coprod.inl) b (fun j => entries j ≫ coprod.inr) i) :
    routes J M f (coprod.desc exit back) b entries := by
  induction b with
  | last p =>
    change entries 0 ≫ f = choice J M p ≫ coprod.desc exit back ≫ coprod.inl
    rw [legs 0, bodyArrows, Fin.cases_zero, coprod.desc_comp]
  | next p rest ih =>
    refine ⟨?_, ih (fun j => entries j.succ) (fun j => ?_)⟩
    · exact legs 0
    · simpa only [bodyArrows, Fin.cases_succ] using legs j.succ

omit [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C] in
private theorem route_exit_feedback {X Y Z I : C} (exit : X ⟶ Z) (feedback : Y ⟶ I) :
    coprod.desc (exit ≫ coprod.inl) (feedback ≫ coprod.inr) =
      coprod.map exit (𝟙 Y) ≫ coprod.map (𝟙 Z) feedback := by
  apply coprod.hom_ext <;> simp

private theorem cfg_fold (s : Blocks Φ A B E D tail) :
    J.map (localInject M (localTypes A B tail) 0) ≫ iterate (cfgStep J M s) =
      iterate (activation J M s) := by
  let R := localTypes A B tail
  let I := labelObj M (List.ofFn R)
  let O := labelObj M [E,D]
  let F := J.obj O ⨿ J.obj I
  let toLocal (i : Fin (A :: B :: tail).length) := J.map (localInject M R i)
  let toC := J.map (labelInject M (L := [E,D]) 0 (rfl : Isotope.SSA.At [E,D] 0 E))
  let toD := J.map (labelInject M (L := [E,D]) 1 (rfl : Isotope.SSA.At [E,D] 1 D))
  let finish : J.obj (M.obj D) ⨿ J.obj (M.obj A) ⟶ F :=
    coprod.desc (toD ≫ coprod.inl) (toLocal 0 ≫ coprod.inr)
  let legs : ∀ i, J.obj (M.obj (R i)) ⟶ F ⨿ J.obj I :=
    Fin.cases (motive := fun j => J.obj (M.obj (R j)) ⟶ F ⨿ J.obj I)
      (choice J M s.header ≫ coprod.desc (toC ≫ coprod.inl ≫ coprod.inl)
        (toLocal (0 : Fin (B :: tail).length).succ ≫ coprod.inr))
      (bodyArrows J M (toD ≫ coprod.inl ≫ coprod.inl) (toLocal 0 ≫ coprod.inr ≫ coprod.inl) s.body
        (fun j => toLocal j.succ ≫ coprod.inr))
  let inner := J.map (labelObjToFinite M R) ≫ dispatch J M R legs
  let flatten : F ⨿ J.obj I ⟶ F := coprod.desc (𝟙 F) coprod.inr
  have atInner (i : Fin (A :: B :: tail).length) : toLocal i ≫ inner = legs i :=
    at_local J M R legs i
  let decode := J.map (labelAppendSplit M (List.ofFn R) [E,D]) ≫ splitMapCoprod J O I
  have atCfg (i : Fin (A :: B :: tail).length) : toLocal i ≫ cfgStep J M s =
      blockArrows J M s i ≫ decode := by
    have step : cfgStep J M s =
        (J.map (labelObjToFinite M R) ≫ dispatch J M R (blockArrows J M s)) ≫ decode :=
      (Category.assoc (J.map (labelObjToFinite M R)) (dispatch J M R (blockArrows J M s)) decode).symm
    rw [step, ← Category.assoc]
    exact congrArg (fun k => k ≫ decode) (at_local J M R (blockArrows J M s) i)
  have localRoute (i : Fin (A :: B :: tail).length) :
      J.map (siteArrow M (localSite R [E,D] i)) ≫ decode = toLocal i ≫ coprod.inr := by
    change J.map (labelInject M i (localSite R [E,D] i).typing) ≫
      J.map (labelAppendSplit M (List.ofFn R) [E,D]) ≫ splitMapCoprod J O I = _
    have route : labelInject M i (localSite R [E,D] i).typing ≫
        labelAppendSplit M (List.ofFn R) [E,D] = localInject M R i ≫ coprod.inr :=
      labelAppendSplit_local M R [E,D] i _ _
    rw [← J.map_comp_assoc, route, J.map_comp, Category.assoc, split_inr]
  have exitRoute (i : Fin ([E,D] : List τ).length) :
      J.map (siteArrow M (externalSite R [E,D] i)) ≫ decode =
        J.map (labelInject M (L := [E,D]) i (by simp [Isotope.SSA.At])) ≫ coprod.inl := by
    have eidx : (externalSite R [E,D] i).index = (A :: B :: tail).length + i.val := by
      simp [externalSite, Nat.add_comm]
    have he := (externalSite R [E,D] i).typing
    rw [eidx] at he
    have e : siteArrow M (externalSite R [E,D] i) = labelInject M _ he := by
      unfold siteArrow
      congr
    change J.map _ ≫ J.map (labelAppendSplit M (List.ofFn R) [E,D]) ≫ splitMapCoprod J O I = _
    rw [e, ← J.map_comp_assoc, labelAppendSplit_exit, J.map_comp, Category.assoc, split_inl]
  have out0 : J.map (siteArrow M (externalSite R [E,D] 0)) ≫ decode = toC ≫ coprod.inl :=
    exitRoute 0
  have out1 : J.map (siteArrow M (externalSite R [E,D] 1)) ≫ decode = toD ≫ coprod.inl :=
    exitRoute 1
  have in0 : (coprod.inl : F ⟶ F ⨿ J.obj I) ≫ flatten = 𝟙 F := coprod.inl_desc _ _
  have in1 : (coprod.inr : J.obj I ⟶ F ⨿ J.obj I) ≫ flatten = coprod.inr :=
    coprod.inr_desc _ _
  have flat : cfgStep J M s = inner ≫ flatten := by
    apply local_ext J M R
    intro i
    change toLocal i ≫ cfgStep J M s = toLocal i ≫ (inner ≫ flatten)
    rw [atCfg, ← (Category.assoc (toLocal i) inner flatten), atInner]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [blockArrows, caseArrow, legs, Fin.cases_zero, Category.assoc, coprod.desc_comp]
      rw [out0, show bodySites A B E D tail 0 = localSite R [E,D] (0 : Fin (B :: tail).length).succ from rfl,
        localRoute, in0, in1, Category.comp_id]
    · simp only [blockArrows, legs, Fin.cases_succ, bodyArrows_post, Category.assoc, bodySites]
      change bodyArrows J M (J.map (siteArrow M (externalSite R [E,D] 1)) ≫ decode)
        (J.map (siteArrow M (localSite R [E,D] 0)) ≫ decode) s.body
        (fun i => J.map (siteArrow M (localSite R [E,D] i.succ)) ≫ decode) j = _
      rw [out1, localRoute 0]
      have exits : toD ≫ (coprod.inl : J.obj O ⟶ F) ≫ coprod.inl ≫ flatten =
          toD ≫ (coprod.inl : J.obj O ⟶ F) := by
        rw [in0, Category.comp_id]
      have back : toLocal 0 ≫ (coprod.inr : J.obj I ⟶ F) ≫ coprod.inl ≫ flatten =
          toLocal 0 ≫ (coprod.inr : J.obj I ⟶ F) := by rw [in0, Category.comp_id]
      rw [exits, back]
      have h : (fun i : Fin (B :: tail).length =>
          J.map (siteArrow M (localSite R [E,D] i.succ)) ≫ decode) =
          (fun i : Fin (B :: tail).length => toLocal i.succ ≫ coprod.inr ≫ flatten) := by
        funext i
        rw [localRoute i.succ, in1]
      rw [h]
  have selected : toLocal (0 : Fin (B :: tail).length).succ ≫ iterate inner =
      bodyFold J M s.body ≫ finish := by
    apply iter_body J M inner finish s.body (fun j => toLocal j.succ)
    apply routes_of_legs J M inner (toD ≫ coprod.inl) (toLocal 0 ≫ coprod.inr)
    intro i
    simpa only [legs, Fin.cases_succ, Category.assoc] using atInner i.succ

  have header : toLocal 0 ≫ iterate inner =
      choice J M s.header ≫ coprod.desc (toC ≫ coprod.inl) (bodyFold J M s.body ≫ finish) := by
    rw [ElgotCategory.fixpoint inner, ← Category.assoc, atInner]
    simp only [legs, Fin.cases_zero, Category.assoc, coprod.desc_comp, coprod.inl_desc,
      coprod.inr_desc]
    rw [← Category.assoc, selected, Category.comp_id (toC ≫ (coprod.inl : J.obj O ⟶ F))]
  have continuation : finish =
      coprod.map toD (𝟙 (J.obj (M.obj A))) ≫ coprod.map (𝟙 (J.obj O)) (toLocal 0) :=
    route_exit_feedback toD (toLocal 0)
  have commute : toLocal 0 ≫ iterate inner =
      activation J M s ≫ coprod.map (𝟙 (J.obj O)) (toLocal 0) := by
    rw [header, continuation]
    simp only [activation, Category.assoc, coprod.desc_comp, coprod.inl_map]
    rw [Category.id_comp (coprod.inl : J.obj O ⟶ F)]
  rw [flat]
  exact close_grouped J (localInject M R 0) inner (activation J M s) commute

variable [FreydCategory.CentralUnit J]

theorem region_denotes (s : Blocks Φ A B E D tail) :
    RegionDenotes J M (regionTyping s) (denote J M s) := by
  have h := cfg_denotes J M s
  rw [cfg_fold J M s] at h
  exact h

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs
