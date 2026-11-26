module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Reindex and factor an interpreted carried step -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification.SingleCfg.Model
open Paper.SingletonReification (packedPair packedDiagonal packedWhiskerRight packedWhiskerLeft)
open CfgEta.TypeCategory.ConstructorReification (fstMap inlMap inrMap)
open CfgEta.TypeCategory.Retained (packedDistributor)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (route_inl route_inr labelInject_payload labelAppendSplit_zero_assoc labelAppendSplit_succ_assoc)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel contextualStep retainEnvironment routeEnvironment retainEnvironment_comp
    retainEnvironment_pre_assoc retainEnvironment_map retainLeft_pre_map_assoc)
open CartesianMonoidalCategory (fst lift_fst_assoc)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft splitMapCoprod)

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

set_option backward.isDefEq.respectTransparency false in
theorem exitSum_inl (S D : τ) :
    inlMap M S (Silmaril.coprod D Silmaril.empty) ≫ exitSum M S D = inrMap M D S := by
  simp only [exitSum, packedExitType, inlMap, inrMap, unpackLabel, Category.assoc,
    Iso.inv_hom_id_assoc, coprod.inl_desc_assoc, labelAppendSplit_zero_assoc,
    coprod.inr_map_assoc]
  rw [reassoc_of% (labelInject_payload M S)]

set_option backward.isDefEq.respectTransparency false in
theorem exitSum_inr_inl (S D : τ) :
    inlMap M D Silmaril.empty ≫ inrMap M S (Silmaril.coprod D Silmaril.empty) ≫ exitSum M S D =
      inlMap M D S := by
  simp only [exitSum, packedExitType, inlMap, inrMap, unpackLabel, Category.assoc,
    Iso.inv_hom_id_assoc, coprod.inr_desc_assoc, coprod.inl_desc_assoc, labelInject_labelMap_assoc,
    labelAppendSplit_succ_assoc, coprod.inl_map_assoc]
  rw [reassoc_of% (labelInject_payload M D)]

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

section RouteFactor

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] (J : V ⥤ C)
  [DistributiveFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
private theorem route_tensor_map {E F L R L' R' : V}
    (e : E ⟶ F) (l : L ⟶ L') (r : R ⟶ R') :
    routeEnvironment J E L R ≫ coprod.map (J.map (e ⊗ₘ l)) (J.map (e ⊗ₘ r)) =
      J.map (e ⊗ₘ coprod.map l r) ≫ routeEnvironment J F L' R' := by
  let route := routeEnvironment J E L R
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : L ⟶ L ⨿ R)) := by
    rw [← route_inl J, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hr : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : R ⟶ L ⨿ R)) := by
    rw [← route_inr J, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- Test the square on the two injections of the original retained sum.
  apply (cancel_epi (inv route)).mp
  change inv route ≫ route ≫ _ = _
  rw [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_map, reassoc_of% hl, ← J.map_comp_assoc]
    have eq : (E ◁ (coprod.inl : L ⟶ L ⨿ R)) ≫ (e ⊗ₘ coprod.map l r) =
        (e ⊗ₘ l) ≫ (F ◁ (coprod.inl : L' ⟶ L' ⨿ R')) := by
      simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, coprod.inl_map, MonoidalCategory.whiskerLeft_comp_assoc,
        MonoidalCategory.whisker_exchange e (coprod.inl : L' ⟶ L' ⨿ R')]
    rw [eq, J.map_comp_assoc, route_inl J]
  · rw [coprod.inr_map, reassoc_of% hr, ← J.map_comp_assoc]
    have eq : (E ◁ (coprod.inr : R ⟶ L ⨿ R)) ≫ (e ⊗ₘ coprod.map l r) =
        (e ⊗ₘ r) ≫ (F ◁ (coprod.inr : R' ⟶ L' ⨿ R')) := by
      simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, coprod.inr_map, MonoidalCategory.whiskerLeft_comp_assoc,
        MonoidalCategory.whisker_exchange e (coprod.inr : R' ⟶ L' ⨿ R')]
    rw [eq, J.map_comp_assoc, route_inr J]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] private theorem map_split {A B C D : V} (f : A ⟶ C) (g : B ⟶ D) :
    splitMapCoprod J A B ≫ coprod.map (J.map f) (J.map g) =
      J.map (coprod.map f g) ≫ splitMapCoprod J C D := by
  apply (cancel_epi (coprodComparison J A B)).mp
  simp only [splitMapCoprod, IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_map, inl_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inl_map,
      J.map_comp_assoc, map_inl_inv_coprodComparison]
  · rw [coprod.inr_map, inr_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inr_map,
      J.map_comp_assoc, map_inr_inv_coprodComparison]

private theorem retain_map {E A B : V} (f : A ⟶ B) :
    retainLeft J (R := E) (J.map f) = J.map (E ◁ f) := by
  simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]

variable (M : TypeModel τ V) {obj : τ → C} (objIso : ∀ A : τ, J.obj (M.obj A) ≅ obj A)

set_option backward.isDefEq.respectTransparency false in
private theorem carriedRoute_value (X S D : τ) :
    let K := packedExitType [S, D]
    Model.carriedRoute J M objIso X S D =
      (objIso (product X K)).inv ≫
      J.map ((M.productIso X K).hom ≫
        M.obj X ◁ (exitSum M S D ≫ (M.coprodIso D S).hom)) ≫
      routeEnvironment J (M.obj X) (M.obj D) (M.obj S) ≫
      coprod.map (J.map (M.productIso X D).inv ≫ (objIso (product X D)).hom)
        (J.map (M.productIso X S).inv ≫ (objIso (product X S)).hom) := by
  let K := packedExitType [S, D]
  let E := ctxObj M [X]
  let e : E ≅ M.obj X := λ_ (M.obj X)
  let l := labelPayloadIso M D
  let r := labelPayloadIso M S
  let f := unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D]
  dsimp only [Model.carriedRoute]
  change (objIso (product X K)).inv ≫ J.map (M.productIso X K).hom ≫
    J.map (e.inv ▷ M.obj K) ≫ retainLeft J (R := E) (J.map f) ≫
    routeEnvironment J E _ _ ≫ coprod.map (carrier J M objIso X D).hom (carrier J M objIso X S).hom = _
  -- Each output comparison strips the singleton label and the unit before packing.
  have arm (A : τ) : (carrier J M objIso X A).hom =
      J.map (e.hom ⊗ₘ (labelPayloadIso M A).hom) ≫
        (J.map (M.productIso X A).inv ≫ (objIso (product X A)).hom) := by
    simp only [carrier, carriedIso, Iso.trans_hom, Functor.mapIso_hom,
      MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.tensorHom_def', J.map_comp_assoc]
    rfl
  rw [retain_map J, arm D, arm S, ← coprod.map_map, ← Category.assoc (routeEnvironment J E _ _),
    route_tensor_map J]
  simp only [Category.assoc, ← J.map_comp_assoc, MonoidalCategory.tensorHom_def']
  congr 1
  congr 1
  congr 1
  simp only [exitSum, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc (unpackLabel M [S, D]) (labelAppendSplit M [S] [D])]
  change (M.productIso X K).hom ≫ e.inv ▷ M.obj K ≫ E ◁ f ≫
      E ◁ coprod.map l.hom r.hom ≫ e.hom ▷ (M.obj D ⨿ M.obj S) =
    (M.productIso X K).hom ≫ M.obj X ◁ (f ≫ coprod.map l.hom r.hom)
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whisker_exchange_assoc e.inv,
    ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem reindexCoprod_of_injections (A B : τ) (output : obj (coprod A B) ≅ obj A ⨿ obj B)
    (left : reindexHom J M objIso (J.map (inlMap M A B)) ≫ output.hom = coprod.inl)
    (right : reindexHom J M objIso (J.map (inrMap M A B)) ≫ output.hom = coprod.inr) :
    J.map (M.coprodIso A B).inv ≫ (objIso (coprod A B)).hom ≫ output.hom =
      splitMapCoprod J (M.obj A) (M.obj B) ≫ coprod.map (objIso A).hom (objIso B).hom := by
  apply (cancel_epi (coprodComparison J (M.obj A) (M.obj B))).mp
  simp only [splitMapCoprod, IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inl_map]
    have h := congrArg (fun f => (objIso A).hom ≫ f) left
    simpa only [inlMap, reindexHom, Category.assoc, Iso.hom_inv_id_assoc] using h
  · rw [inr_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inr_map]
    have h := congrArg (fun f => (objIso B).hom ≫ f) right
    simpa only [inrMap, reindexHom, Category.assoc, Iso.hom_inv_id_assoc] using h

set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_factor (X S D : τ)
    (output : obj (coprod (product X D) (product X S)) ≅ obj (product X D) ⨿ obj (product X S))
    (output_agrees :
      J.map (M.coprodIso (product X D) (product X S)).inv ≫
        (objIso (coprod (product X D) (product X S))).hom ≫ output.hom =
      splitMapCoprod J (M.obj (product X D)) (M.obj (product X S)) ≫
        coprod.map (objIso (product X D)).hom (objIso (product X S)).hom) :
    let K := packedExitType [S, D]
    let U := coprod D S
    Model.carriedRoute J M objIso X S D =
      reindexHom J M objIso (J.map (packedWhiskerLeft M X K U (exitSum M S D))) ≫
      reindexHom J M objIso (J.map (packedDistributor M X D S)) ≫
      output.hom := by
  rw [carriedRoute_value J M objIso]
  simp only [reindexHom, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [packedWhiskerLeft, packedDistributor]
  simp only [J.map_comp, Category.assoc]
  rw [output_agrees]
  simp only [← J.map_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [routeEnvironment, MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc]
  rw [← map_split_assoc J, coprod.map_map]

end RouteFactor

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CarriedModel
