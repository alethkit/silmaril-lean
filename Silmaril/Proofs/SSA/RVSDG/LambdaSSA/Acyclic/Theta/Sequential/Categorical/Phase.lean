module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Defs

/-! # Factor a one-way two-phase Elgot dispatcher -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Proofs

open CategoryTheory CategoryTheory.Limits
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

universe v w h k
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (F : V ⥤ C) [ElgotFreydCategory F]

variable {X Y : V} {P O : C}

@[reassoc] theorem phase_inl (first : F.obj X ⟶ P ⨿ F.obj X) (second : F.obj Y ⟶ O ⨿ F.obj Y)
    (handoff : P ⟶ F.obj Y) :
    F.map (coprod.inl : X ⟶ X ⨿ Y) ≫ phaseStep F first second handoff =
      first ≫ coprod.desc (handoff ≫ F.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.inr)
        (F.map (coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.inr) := by
  unfold phaseStep
  rw [← Category.assoc, splitMapCoprod, map_inl_inv_coprodComparison, coprod.inl_desc]

@[reassoc] theorem phase_inr (first : F.obj X ⟶ P ⨿ F.obj X) (second : F.obj Y ⟶ O ⨿ F.obj Y)
    (handoff : P ⟶ F.obj Y) :
    F.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ phaseStep F first second handoff =
      second ≫ coprod.map (𝟙 O) (F.map (coprod.inr : Y ⟶ X ⨿ Y)) := by
  unfold phaseStep
  rw [← Category.assoc, splitMapCoprod, map_inr_inv_coprodComparison, coprod.inr_desc]

/-- Codiagonal separates a one-way phase transition from feedback local to
each phase. The two step arrows and the handoff can be computations. -/
theorem iterate_phases (first : F.obj X ⟶ P ⨿ F.obj X)
    (second : F.obj Y ⟶ O ⨿ F.obj Y) (handoff : P ⟶ F.obj Y) :
    F.map (coprod.inl : X ⟶ X ⨿ Y) ≫ iterate (phaseStep F first second handoff) =
      iterate first ≫ handoff ≫ iterate second := by
  let S := F.obj (X ⨿ Y)
  let left := F.map (coprod.inl : X ⟶ X ⨿ Y)
  let right := F.map (coprod.inr : Y ⟶ X ⨿ Y)
  let leaveFirst : P ⟶ O ⨿ S := handoff ≫ right ≫ coprod.inr
  let leaveSecond : O ⟶ O ⨿ S := coprod.inl
  let f := first ≫ coprod.map leaveFirst (𝟙 (F.obj X))
  let g := second ≫ coprod.map leaveSecond (𝟙 (F.obj Y))
  let grouped : S ⟶ (O ⨿ S) ⨿ S := splitMapCoprod F X Y ≫ coprod.desc
    (f ≫ coprod.map (𝟙 (O ⨿ S)) left) (g ≫ coprod.map (𝟙 (O ⨿ S)) right)
  have squareL : f ≫ coprod.map (𝟙 (O ⨿ S)) left = left ≫ grouped := by
    dsimp only [left, grouped]
    rw [← Category.assoc, splitMapCoprod, map_inl_inv_coprodComparison, coprod.inl_desc]
  have squareR : g ≫ coprod.map (𝟙 (O ⨿ S)) right = right ≫ grouped := by
    dsimp only [right, grouped]
    rw [← Category.assoc, splitMapCoprod, map_inr_inv_coprodComparison, coprod.inr_desc]
  have leftIter : left ≫ iterate grouped = iterate first ≫ leaveFirst :=
    ((ElgotFreydCategory.pure_uniformity F f grouped coprod.inl squareL).symm).trans
      (ElgotCategory.naturality first leaveFirst).symm
  have rightIter : right ≫ iterate grouped = iterate second ≫ leaveSecond :=
    ((ElgotFreydCategory.pure_uniformity F g grouped coprod.inr squareR).symm).trans
      (ElgotCategory.naturality second leaveSecond).symm
  let collapse : (O ⨿ S) ⨿ S ⟶ O ⨿ S := coprod.desc (𝟙 _) coprod.inr
  have flat : grouped ≫ collapse = phaseStep F first second handoff := by
    simp only [grouped, phaseStep, Category.assoc, coprod.desc_comp]
    apply congrArg (fun arrow => splitMapCoprod F X Y ≫ arrow)
    apply coprod.hom_ext
    · simp only [coprod.inl_desc, f, Category.assoc]
      apply congrArg (fun arrow => first ≫ arrow)
      apply coprod.hom_ext
      · simp [collapse, leaveFirst, right]
      · simp [collapse, left]; rfl
    · simp only [coprod.inr_desc, g, Category.assoc]
      apply congrArg (fun arrow => second ≫ arrow)
      apply coprod.hom_ext <;> simp [collapse, leaveSecond, right] <;> rfl
  have done : right ≫ iterate (iterate grouped) = iterate second := by
    rw [ElgotCategory.fixpoint (iterate grouped), ← Category.assoc, rightIter]
    simp [leaveSecond]
  change left ≫ iterate (phaseStep F first second handoff) = _
  rw [← flat, ← ElgotCategory.codiagonal, ElgotCategory.fixpoint (iterate grouped),
    ← Category.assoc, leftIter]
  simp only [leaveFirst, Category.assoc, coprod.inr_desc, done]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Proofs
