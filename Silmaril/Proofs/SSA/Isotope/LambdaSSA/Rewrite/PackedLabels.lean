module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

/-! # The interpretation of the packed exit type is a finite coproduct -/

public section

universe v u w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Region (packedExitType)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)

private theorem labelInject_get (L : LCtx τ) (i : Fin L.length) :
    labelInject M i (labelAt_get L i) =
      Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i := by
  unfold labelInject
  simp

private theorem labelHom_ext {L : LCtx τ} {Y : V} {f g : labelObj M L ⟶ Y}
    (h : ∀ (i : Nat) (A : τ) (hi : At L i A), labelInject M i hi ≫ f = labelInject M i hi ≫ g) :
    f = g := by
  apply Sigma.hom_ext
  intro i
  rw [← labelInject_get]
  exact h i (L.get i) (labelAt_get L i)

@[reassoc] theorem labelInject_packLabel {L : LCtx τ} {i : Nat} {A : τ} (hi : At L i A) :
    labelInject M i hi ≫ packLabel M L = packedLabelInject M i hi := by
  obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp hi
  let j : Fin L.length := ⟨i, hlt⟩
  change L.get j = A at hh
  subst A
  change labelInject M j (labelAt_get L j) ≫ _ = _
  rw [labelInject_get, packLabel, Sigma.ι_comp_desc]

@[reassoc] theorem packedLabelInject_unpackLabel {L : LCtx τ} {i : Nat} {A : τ} (hi : At L i A) :
    packedLabelInject M i hi ≫ unpackLabel M L = labelInject M i hi := by
  induction L generalizing i with
  | nil => simp [At] at hi
  | cons B L ih =>
    cases i with
    | zero =>
      have h : B = A := Option.some.inj hi
      subst A
      simp [packedLabelInject, unpackLabel]
    | succ i =>
      simp only [packedLabelInject, unpackLabel, Category.assoc, Iso.inv_hom_id_assoc,
        coprod.inr_desc]
      rw [← Category.assoc, ih (show At L i A from hi), labelInject_labelMap]

theorem packLabel_unpackLabel (L : LCtx τ) : packLabel M L ≫ unpackLabel M L = 𝟙 _ := by
  apply labelHom_ext M
  intro i A hi
  rw [labelInject_packLabel_assoc, packedLabelInject_unpackLabel, Category.comp_id]

private theorem shift_packLabel (A : τ) (L : LCtx τ) :
    labelMap M (Silmaril.Isotope.SSA.Ren.wk L A) ≫ packLabel M (A :: L) =
      packLabel M L ≫ coprod.inr ≫ (M.coprodIso A (packedExitType L)).inv := by
  apply labelHom_ext M
  intro i B hi
  rw [labelInject_labelMap_assoc, labelInject_packLabel, labelInject_packLabel_assoc]
  rfl

theorem unpackLabel_packLabel (L : LCtx τ) : unpackLabel M L ≫ packLabel M L = 𝟙 _ := by
  induction L with
  | nil => exact M.emptyIsInitial.hom_ext _ _
  | cons A L ih =>
    let e : M.obj (packedExitType (A :: L)) ≅ M.obj A ⨿ M.obj (packedExitType L) :=
      M.coprodIso A (packedExitType L)
    apply (cancel_epi e.inv).mp
    change e.inv ≫ (e.hom ≫ coprod.desc (labelInject M 0 rfl)
      (unpackLabel M L ≫ labelMap M (Silmaril.Isotope.SSA.Ren.wk L A))) ≫ packLabel M (A :: L) =
      e.inv ≫ 𝟙 _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
    apply coprod.hom_ext
    · simp [Category.assoc, labelInject_packLabel, packedLabelInject, e]
    · simp only [Category.assoc, coprod.inr_desc_assoc, shift_packLabel, ← Category.assoc (unpackLabel M L),
        ih, Category.id_comp, e]

@[reassoc] theorem labelInject_singletonLabelPayload (A : τ) :
    labelInject M 0 (L := [A]) (A := A) rfl ≫ singletonLabelPayload M A = 𝟙 _ := by
  rw [show labelInject M 0 (L := [A]) (A := A) rfl =
      labelInject M (0 : Fin 1) (labelAt_get [A] 0) from rfl,
    labelInject_get, singletonLabelPayload, Sigma.ι_comp_desc]
  simp

theorem singletonLabelPayload_labelInject (A : τ) :
    singletonLabelPayload M A ≫ labelInject M 0 (L := [A]) (A := A) rfl = 𝟙 _ := by
  apply labelHom_ext M
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [labelInject_singletonLabelPayload_assoc, Category.comp_id]
  | succ i => simp [At] at hi

theorem packLabelExit_unpackLabelExit (L : LCtx τ) :
    packLabelExit M L ≫ unpackLabelExit M L = 𝟙 _ := by
  simp only [packLabelExit, unpackLabelExit, Category.assoc, labelInject_singletonLabelPayload_assoc,
    packLabel_unpackLabel]

theorem unpackLabelExit_packLabelExit (L : LCtx τ) :
    unpackLabelExit M L ≫ packLabelExit M L = 𝟙 _ := by
  simp only [packLabelExit, unpackLabelExit, Category.assoc, ← Category.assoc (unpackLabel M L),
    unpackLabel_packLabel, Category.id_comp, singletonLabelPayload_labelInject]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
