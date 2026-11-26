module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

theorem square {A B : Q} (g : A ⟶ B ⨿ A) :
    step g ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ g := by
  apply coprod.hom_ext
  · simp [step]
  · apply coprod.hom_ext <;> simp [step]

private noncomputable def cut {A B : Q} (g : A ⟶ B ⨿ A) :
    A ⨿ (A ⨿ A) ⟶ (B ⨿ A) ⨿ (A ⨿ A) :=
  coprod.desc (g ≫ coprod.map coprod.inl coprod.inl)
    (coprod.desc (g ≫ coprod.map coprod.inl coprod.inr) (g ≫ coprod.inl))

private theorem cut_assoc {A B : Q} (g : A ⟶ B ⨿ A) :
    cut Seed g ≫ (coprod.associator B A (A ⨿ A)).hom = step g := by
  apply coprod.hom_ext
  · simp only [cut, step, coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc]
    congr 1
    apply coprod.hom_ext <;> simp [coprod.associator]
  · apply coprod.hom_ext
    · simp only [cut, step, coprod.inr_desc_assoc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inl_desc, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp [coprod.associator]
    · simp only [cut, step, coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp [coprod.associator]

theorem iterate_eq {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = coprod.desc (I (triple g))
      (coprod.desc ((g ≫ coprod.desc coprod.inl g) ≫ coprod.desc (𝟙 B) (I (triple g)))
        (g ≫ coprod.desc (𝟙 B) (I (triple g)))) := by
  let right : A ⨿ A ⟶ (B ⨿ A) ⨿ (A ⨿ A) := coprod.inr ≫ cut Seed g
  have rightLast : (coprod.inr : A ⟶ A ⨿ A) ≫ I right = g := by
    rw [iterateChosen_fixpoint Seed right]
    simp [right, cut]
  have rightMiddle : (coprod.inl : A ⟶ A ⨿ A) ≫ I right =
      g ≫ coprod.desc coprod.inl g := by
    have row : (coprod.inl : A ⟶ A ⨿ A) ≫ right =
        g ≫ coprod.map coprod.inl coprod.inr := by simp [right, cut]
    conv_lhs => rw [iterateChosen_fixpoint Seed right]
    rw [← Category.assoc, row]
    simp [rightLast]
  have rightEq : I right = coprod.desc (g ≫ coprod.desc coprod.inl g) g :=
    coprod.hom_ext (by simpa using rightMiddle) (by simpa using rightLast)
  have first : (coprod.inl : A ⟶ A ⨿ (A ⨿ A)) ≫ cut Seed g ≫
      coprod.desc (𝟙 (B ⨿ A)) (I right) = triple g := by
    simp [cut, rightEq]
  rw [← cut_assoc Seed g, iterateChosen_rows Seed]
  change coprod.desc (I ((coprod.inl ≫ cut Seed g) ≫ coprod.desc (𝟙 _) (I right)))
    (I right ≫ coprod.desc (𝟙 B) (I ((coprod.inl ≫ cut Seed g) ≫ coprod.desc (𝟙 _) (I right)))) = _
  rw [Category.assoc, first, rightEq, coprod.desc_comp]

theorem fold_iff_triple {A B : Q} (g : A ⟶ B ⨿ A) :
    I (step g) = fold A ≫ I g ↔ I (triple g) = I g := by
  rw [iterate_eq Seed g]
  constructor
  · intro h
    simpa using congrArg ((coprod.inl : A ⟶ A ⨿ (A ⨿ A)) ≫ ·) h
  · intro h
    rw [h]
    have unfold : g ≫ coprod.desc (𝟙 B) (I g) = I g := (iterateChosen_fixpoint Seed g).symm
    apply coprod.hom_ext
    · simp
    · apply coprod.hom_ext
      · simp only [coprod.inr_desc, coprod.inl_desc, Category.id_comp, Category.assoc, coprod.desc_comp,
          unfold]
      · simp [unfold]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycle
