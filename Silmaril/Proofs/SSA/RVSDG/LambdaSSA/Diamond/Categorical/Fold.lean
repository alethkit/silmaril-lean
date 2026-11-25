module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Dispatcher

/-! # Grouping the diamond CFG into nested γ and θ -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Isotope.LambdaSSA.Semantics.Categorical
  (RegionDenotes labelObj labelInject labelObjToFinite labelObjToFinite_local)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain.Categorical (call choice cfgStepOf cfgStepOf_at localInject local_ext
  decodeLabels decode_local decode_exit dispatch dispatch_at_assoc group_feedback)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k

section Iteration

variable {C : Type w} [Category.{k} C] [HasFiniteCoproducts C] [Iteration C] [ElgotCategory C]
variable {I O P X Y Z : C}

private theorem unfold_at (f : I ⟶ O ⨿ I) (atLabel : P ⟶ I) {step : P ⟶ O ⨿ I}
    (h : atLabel ≫ f = step) :
    atLabel ≫ iterate f = step ≫ coprod.desc (𝟙 O) (iterate f) := by
  rw [← h, Category.assoc]
  exact congrArg (fun k => atLabel ≫ k) (ElgotCategory.fixpoint f)

private theorem continue_at (f : I ⟶ O ⨿ I) (atLabel : P ⟶ I) (next : P ⟶ I)
    (h : atLabel ≫ f = next ≫ coprod.inr) :
    atLabel ≫ iterate f = next ≫ iterate f := by
  rw [unfold_at f atLabel h, Category.assoc, coprod.inr_desc]

omit [Iteration C] [ElgotCategory C] in
private theorem exit_feedback (exit : X ⟶ Z) (feedback : Y ⟶ I) :
    coprod.desc (exit ≫ coprod.inl) (feedback ≫ coprod.inr) =
      coprod.map exit (𝟙 Y) ≫ coprod.map (𝟙 Z) feedback := by
  apply coprod.hom_ext <;> simp

end Iteration

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B X Y K E D : τ}

private theorem fold (s : Blocks Φ A B X Y K E D) :
    J.map (localInject M (localTypes A B X Y K) 0) ≫
        iterate (cfgStepOf J M (localTypes A B X Y K) [E,D] (arrows J M s (labelEdges J M))) =
      iterate (activation J M s) := by
  let R := localTypes A B X Y K
  let I := labelObj M (List.ofFn R)
  let O := labelObj M [E,D]
  let F := J.obj O ⨿ J.obj I
  let place (i : Fin 5) := J.map (localInject M R i)
  let en : J.obj (M.obj A) ⟶ J.obj I := place 0
  let cl : J.obj (M.obj B) ⟶ J.obj I := place 1
  let l : J.obj (M.obj X) ⟶ J.obj I := place 2
  let r : J.obj (M.obj Y) ⟶ J.obj I := place 3
  let hub : J.obj (M.obj K) ⟶ J.obj I := place 4
  let out0 : J.obj (M.obj E) ⟶ J.obj O := J.map (labelInject M (L := [E,D]) 0 rfl)
  let out1 : J.obj (M.obj D) ⟶ J.obj O := J.map (labelInject M (L := [E,D]) 1 rfl)
  let finish : J.obj (M.obj D) ⨿ J.obj (M.obj A) ⟶ F :=
    coprod.desc (out1 ≫ coprod.inl) (en ≫ coprod.inr)
  let edges : Edges J M A B X Y K E D (F ⨿ J.obj I) :=
    ⟨out0 ≫ coprod.inl ≫ coprod.inl, cl ≫ coprod.inr, l ≫ coprod.inr, r ≫ coprod.inr,
      hub ≫ coprod.inr, out1 ≫ coprod.inl ≫ coprod.inl, en ≫ coprod.inr ≫ coprod.inl⟩
  let inner := J.map (labelObjToFinite M R) ≫ dispatch J M R (arrows J M s edges)
  let flatten : F ⨿ J.obj I ⟶ F := coprod.desc (𝟙 F) coprod.inr
  let raw : Edges J M A B X Y K E D (J.obj (labelObj M (List.ofFn R ++ [E,D]))) := labelEdges J M
  have atInner (i : Fin 5) : place i ≫ inner = arrows J M s edges i := by
    change J.map (localInject M R i) ≫ (J.map (labelObjToFinite M R) ≫
        dispatch J M R (arrows J M s edges)) = _
    rw [← J.map_comp_assoc, localInject, labelObjToFinite_local, LinearChain.Categorical.dispatch_at]
  have mergeLeft : (coprod.inl : F ⟶ F ⨿ J.obj I) ≫ flatten = 𝟙 F := coprod.inl_desc _ _
  have mergeRight : (coprod.inr : J.obj I ⟶ F ⨿ J.obj I) ≫ flatten = coprod.inr := coprod.inr_desc _ _
  have edgeEq : raw.post J M (decodeLabels J M R [E,D]) = edges.post J M flatten := by
    dsimp only [raw, labelEdges, Edges.post, edges]
    congr 1
    · rw [decode_exit J M R [E,D] (0 : Fin 2) rfl]
      change out0 ≫ (coprod.inl : J.obj O ⟶ F) = (_ ≫ _ ≫ _) ≫ flatten
      rw [Category.assoc, Category.assoc, mergeLeft, Category.comp_id]
    · rw [decode_local J M R [E,D] 1, Category.assoc, mergeRight]
    · rw [decode_local J M R [E,D] 2, Category.assoc, mergeRight]
    · rw [decode_local J M R [E,D] 3, Category.assoc, mergeRight]
    · rw [decode_local J M R [E,D] 4, Category.assoc, mergeRight]
    · rw [decode_exit J M R [E,D] (1 : Fin 2) rfl]
      change out1 ≫ (coprod.inl : J.obj O ⟶ F) = (_ ≫ _ ≫ _) ≫ flatten
      rw [Category.assoc, Category.assoc, mergeLeft, Category.comp_id]
    · rw [decode_local J M R [E,D] 0]
      change en ≫ (coprod.inr : J.obj I ⟶ F) = (_ ≫ _ ≫ _) ≫ flatten
      rw [Category.assoc, Category.assoc, mergeLeft, Category.comp_id]
  have flat : cfgStepOf J M R [E,D] (arrows J M s raw) = inner ≫ flatten := by
    apply local_ext J M R
    intro i
    change place i ≫ cfgStepOf J M R [E,D] (arrows J M s raw) = place i ≫ (inner ≫ flatten)
    rw [cfgStepOf_at, ← (Category.assoc (place i) inner flatten), atInner,
      arrows_post, arrows_post, edgeEq]
  let after : J.obj (M.obj K) ⟶ F := choice J M s.join ≫ finish
  have atJoin : hub ≫ iterate inner = after := by
    have one : hub ≫ inner = choice J M s.join ≫
        coprod.desc (out1 ≫ coprod.inl ≫ coprod.inl) (en ≫ coprod.inr ≫ coprod.inl) := atInner 4
    rw [unfold_at inner hub one]
    change (choice J M s.join ≫ _) ≫ _ = choice J M s.join ≫ finish
    simp only [Category.assoc, coprod.desc_comp, coprod.inl_desc, finish]
    rw [Category.comp_id (coprod.inl : J.obj O ⟶ F), Category.comp_id (coprod.inr : J.obj I ⟶ F)]
  have atLeft : l ≫ iterate inner = call J M s.diamond.left ≫ after := by
    have one : l ≫ inner = (call J M s.diamond.left ≫ hub) ≫ coprod.inr :=
      (atInner 2).trans (Category.assoc _ _ _).symm
    rw [continue_at inner l _ one, Category.assoc, atJoin]
  have atRight : r ≫ iterate inner = call J M s.diamond.right ≫ after := by
    have one : r ≫ inner = (call J M s.diamond.right ≫ hub) ≫ coprod.inr :=
      (atInner 3).trans (Category.assoc _ _ _).symm
    rw [continue_at inner r _ one, Category.assoc, atJoin]
  have atClassifier : cl ≫ iterate inner = diamond J M s.diamond ≫ after := by
    have one : cl ≫ inner = choice J M s.diamond.classifier ≫
        coprod.desc (l ≫ coprod.inr) (r ≫ coprod.inr) := atInner 1
    rw [unfold_at inner cl one]
    simp only [diamond, Category.assoc, coprod.desc_comp, coprod.inr_desc, atLeft, atRight]
  have atHeader : en ≫ iterate inner =
      choice J M s.header ≫ coprod.desc (out0 ≫ coprod.inl) (diamond J M s.diamond ≫ after) := by
    have one : en ≫ inner = choice J M s.header ≫
        coprod.desc (out0 ≫ coprod.inl ≫ coprod.inl) (cl ≫ coprod.inr) := atInner 0
    rw [unfold_at inner en one]
    simp only [Category.assoc, coprod.desc_comp, coprod.inl_desc, coprod.inr_desc, atClassifier]
    rw [Category.comp_id (coprod.inl : J.obj O ⟶ F)]
  have square : en ≫ iterate inner = activation J M s ≫ coprod.map (𝟙 (J.obj O)) en := by
    have normalize : finish = coprod.map out1 (𝟙 (J.obj (M.obj A))) ≫ coprod.map (𝟙 (J.obj O)) en :=
      exit_feedback out1 en
    rw [atHeader]
    simp only [after, normalize, activation, Category.assoc, coprod.desc_comp, coprod.inl_map]
    rw [Category.id_comp (coprod.inl : J.obj O ⟶ F)]
  change en ≫ iterate (cfgStepOf J M R [E,D] (arrows J M s raw)) = _
  rw [flat]
  exact group_feedback J (localInject M R 0) inner (activation J M s) square

variable [FreydCategory.CentralUnit J]

theorem region_denotes (s : Blocks Φ A B X Y K E D) :
    RegionDenotes J M (regionTyping s) (denote J M s) := by
  have h := cfg_denotes J M s
  rw [fold J M s] at h
  exact h

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Proofs
