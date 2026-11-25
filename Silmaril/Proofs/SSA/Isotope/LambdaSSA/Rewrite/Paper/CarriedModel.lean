module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

/-! # Reindex and factor an interpreted carried step -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification.SingleCfg.Model
open Paper.SingletonReification (packedPair packedDiagonal packedWhiskerRight)
open CfgEta.TypeCategory.ConstructorReification (fstMap)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel contextualStep retainEnvironment routeEnvironment retainEnvironment_comp
    retainEnvironment_pre_assoc retainEnvironment_map retainLeft_pre_map_assoc)
open CartesianMonoidalCategory (fst lift_fst_assoc)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

universe u u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ]

section Prefix

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

set_option backward.isDefEq.respectTransparency false in
theorem packedPair_id_right {P X : τ} (f : M.obj P ⟶ M.obj X) :
    packedPair M P X P f (𝟙 (M.obj P)) = packedDiagonal M P ≫ packedWhiskerRight M P P X f := by
  simp only [packedPair, packedDiagonal, packedWhiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (CartesianMonoidalCategory.lift _ _) (f ▷ M.obj P),
    CartesianMonoidalCategory.lift_whiskerRight, Category.id_comp]

end Prefix

section StepFactor

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) {obj : τ → C} (objIso : ∀ A : τ, J.obj (M.obj A) ≅ obj A)
  {X S D : τ}

set_option backward.isDefEq.respectTransparency false in
theorem reindexRetainLeft_tensorIso {R A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    reindexHom J M objIso (J.map (M.productIso R A).hom ≫ retainLeft J (R := M.obj R) f ≫
      J.map (M.productIso R B).inv) =
    (packedTensorIso J M objIso R A).inv ≫ (J.obj (M.obj R) ◁ f) ≫
      (packedTensorIso J M objIso R B).hom := by
  unfold reindexHom
  simp only [retainLeft, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem reindexPackedWhiskerRight_tensorIso {R A B : τ} (f : M.obj A ⟶ M.obj B) :
    reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
    (packedTensorIso J M objIso A R).inv ≫ (J.map f ▷ J.obj (M.obj R)) ≫
      (packedTensorIso J M objIso B R).hom := by
  unfold reindexHom
  have naturality := Functor.StrongPremonoidal.tensor_naturality_left (J := J) f (M.obj R)
  simp only [packedWhiskerRight, Functor.map_comp, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (J.map f ▷ J.obj (M.obj R)), naturality]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem capturePrefix_factor (X S : τ) :
    let E := ctxObj M [X]
    let P := product X S
    (carrier J M objIso X S).inv ≫
      retainEnvironment J (fst E (labelObj M [S])) (J.map (carriedIso M X S).hom) ≫
      J.map ((λ_ (M.obj X)).hom ▷ M.obj P) ≫ J.map (M.productIso X P).inv ≫
      (objIso (product X P)).hom = capturePrefix J M objIso X S := by
  dsimp only [carrier, Iso.trans_inv, Functor.mapIso_inv, ctxObj]
  rw [Category.assoc, retainEnvironment_pre_assoc J, ← J.map_comp, Iso.inv_hom_id, retainEnvironment_map]
  simp only [← J.map_comp_assoc]
  congr 3
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst, lift_fst_assoc,
      CartesianMonoidalCategory.lift_fst]
    let kIso : ctxObj M [X] ≅ M.obj X := λ_ (M.obj X)
    rw [Category.assoc]
    change (carriedIso M X S).inv ≫ fst (ctxObj M [X]) (labelObj M [S]) ≫ kIso.hom = _
    simp only [carriedIso, labelPayloadIso, Iso.trans_inv, Iso.symm_inv,
      MonoidalCategory.whiskerLeftIso_inv, MonoidalCategory.whiskerRightIso_inv, Category.assoc]
    change (M.productIso X S).hom ≫ (kIso.inv ▷ M.obj S) ≫
      (ctxObj M [X] ◁ labelInject M 0 rfl) ≫ fst (ctxObj M [X]) (labelObj M [S]) ≫ kIso.hom = _
    simp only [CartesianMonoidalCategory.whiskerLeft_fst_assoc,
      CartesianMonoidalCategory.whiskerRight_fst_assoc, Iso.inv_hom_id, Category.comp_id, fstMap]

  · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_snd]

set_option backward.isDefEq.respectTransparency false in
theorem carriedStep_factor_retained
    (b : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    carriedStep J M objIso X S D b =
      capturePrefix J M objIso X S ≫
        reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
          retainLeft J (R := M.obj X) b ≫ J.map (M.productIso X (packedExitType [S, D])).inv) ≫
        carriedRoute J M objIso X S D := by
  let E := ctxObj M [X]
  let P := product X S
  let K := packedExitType [S, D]
  let kIso : E ≅ M.obj X := λ_ (M.obj X)
  let intro := J.map (carriedIso M X S).hom
  let split := J.map (unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D])
  let state := carrier J M objIso X S
  let result := carrier J M objIso X D
  change state.inv ≫ contextualStep J (intro ≫ b ≫ split) ≫ coprod.map result.hom state.hom = _
  have prefixEq := capturePrefix_factor J M objIso X S
  change state.inv ≫ retainEnvironment J (fst E (labelObj M [S])) intro ≫
    J.map (kIso.hom ▷ M.obj P) ≫ J.map (M.productIso X P).inv ≫
      (objIso (product X P)).hom = _ at prefixEq
  rw [contextualStep, ← Category.assoc intro b split, retainEnvironment_comp, retainEnvironment_comp,
    ← prefixEq]
  change _ = _ ≫ ((objIso (product X P)).inv ≫ (J.map (M.productIso X P).hom ≫
    retainLeft J (R := M.obj X) b ≫ J.map (M.productIso X K).inv) ≫ (objIso (product X K)).hom) ≫
    ((objIso (product X K)).inv ≫ J.map (M.productIso X K).hom ≫
    J.map (kIso.inv ▷ M.obj K) ≫ retainLeft J (R := E) split ≫
    routeEnvironment J E (labelObj M [D]) (labelObj M [S]) ≫ coprod.map result.hom state.hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← J.map_comp_assoc, Iso.inv_hom_id_assoc]
  rw [Iso.inv_hom_id, Category.comp_id, retainLeft_pre_map_assoc J kIso.hom b, ← J.map_comp_assoc,
    ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id, MonoidalCategory.id_whiskerRight,
    J.map_id, Category.id_comp]

end StepFactor

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel
