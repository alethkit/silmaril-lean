module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Separate structural dispatch and iteration transport -/

public section

universe u v u₁ v₁ w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification (ModelComparisons packedPair)
open Paper.RetainedCase (reindexHom)
open CfgEta.TypeCategory (productSndBranches seqValueBranches caseValueBranches)
open Paper.PackedBody (applyPacked_typed unpack_applyPacked)
open Paper.RetainedLet (unpackBody_typed)
open Paper.RetainedCase (assembleCase_ofRegion)
open SyntacticCategory (iterateRegion_valueBranches)
open CfgEta.TypeCategory.ConstructorReification (sndMap fstMap inlMap inrMap)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel contextualStep retainEnvironment routeEnvironment
    extend_postmap case_pre_map retainEnvironment_comp retainEnvironment_pre_assoc retainEnvironment_map
    retainLeft_pre_map_assoc)
open CartesianMonoidalCategory (fst snd lift_fst_assoc)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open SingletonDispatcher (route_inl route_inr labelInject_payload labelAppendSplit_zero_assoc
  labelAppendSplit_succ_assoc)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop extend splitMapCoprod retainLeft)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

set_option backward.isDefEq.respectTransparency false in
theorem canonical_reindex {U V X Y : Comp} (state : U ≅ X) (result : V ≅ Y)
    (step : U ⟶ V ⨿ U) :
    state.inv ≫ Paper.TypeCategory.iterate step ≫ result.hom =
      Paper.TypeCategory.iterate (reindexStep state result step) := by
  rw [Paper.TypeCategory.iterate_naturality, reindexStep]
  let tail := step ≫ coprod.map result.hom state.hom
  rw [Paper.TypeCategory.iterate_roll state.inv tail]
  congr 2
  dsimp only [tail]
  rw [Category.assoc]
  congr 1
  apply coprod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private theorem empty_unique {D : τ} (f g : ofType (Φ := Φ) (Silmaril.empty : τ) ⟶ ofType D) :
    f = g := by
  obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
  obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
  exact (ofRegion_eq_iff _ _).2 (.cfgEta (.native (.initial (.var (i := 0) rfl) hf.hasType hg.hasType)))

set_option backward.isDefEq.respectTransparency false in
private theorem exact_inl {A B : τ} {Y : Comp} (g : ofType (Φ := Φ) A ⟶ Y)
    (h : ofType (Φ := Φ) B ⟶ Y) :
    (sumCofan A B).inl ≫ (sumIso A B).hom ≫ coprod.desc g h = g := by
  rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
private theorem exact_inr {A B : τ} {Y : Comp} (g : ofType (Φ := Φ) A ⟶ Y)
    (h : ofType (Φ := Φ) B ⟶ Y) :
    (sumCofan A B).inr ≫ (sumIso A B).hom ≫ coprod.desc g h = h := by
  rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
theorem exitSum_ofRegion (S D : τ) :
    exitSumArrow (Φ := Φ) S D = ofRegion (τ := τ) (exitDecoder_typed S D) := by
  unfold exitSumArrow
  rw [sumCofan_inl, sumCofan_inr, coprod_desc_ofRegion, coprod_desc_ofRegion]

set_option backward.isDefEq.respectTransparency false in
private theorem dispatch_ofRegion {X A B D : τ} {e g h : Region Φ}
    (he : ValueBranches [X] e [Silmaril.coprod A B])
    (hg : ValueBranches [Silmaril.product X A] g [D])
    (hh : ValueBranches [Silmaril.product X B] h [D]) :
    dispatchArrow (ofRegion (τ := τ) he) (ofRegion (τ := τ) hg) (ofRegion (τ := τ) hh) =
      ofRegion (τ := τ) (Paper.RetainedCase.assembleCase_typed he (applyPacked_typed hg) (applyPacked_typed hh)) := by
  have arms := coprod_desc_ofRegion
    (unpackBody_typed (applyPacked_typed hg)) (unpackBody_typed (applyPacked_typed hh))
  rw [(ofRegion_eq_iff _ hg).2 (unpack_applyPacked hg), (ofRegion_eq_iff _ hh).2 (unpack_applyPacked hh)] at arms
  have assembled := assembleCase_ofRegion he (applyPacked_typed hg) (applyPacked_typed hh)
  unfold Paper.RetainedCase.assembledCaseArrow at assembled
  unfold dispatchArrow
  rw [arms]
  simpa only [Category.assoc] using assembled

set_option backward.isDefEq.respectTransparency false in
theorem canonicalAssembly_ofRegion {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]) :
    canonicalAssembly (ofRegion (τ := τ) he)
      (ofRegion (τ := τ) hb ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom) =
      ofRegion (τ := τ) (canonicalRegion_typed he hb) := by
  let hd := productSndBranches (Φ := Φ) X D
  have hLoop : Paper.TypeCategory.iterate
      (ofRegion (τ := τ) hb ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom) =
      ofRegion (τ := τ) (iterateRegion_valueBranches hb) := by
    unfold Paper.TypeCategory.iterate
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, iterateSum_ofRegion]
  dsimp only [canonicalAssembly]
  rw [exitSum_ofRegion, hLoop,
    ofRegion_comp he (exitDecoder_typed S D) (seqValueBranches he (exitDecoder_typed S D)),
    ofRegion_comp (iterateRegion_valueBranches hb) hd (seqValueBranches (iterateRegion_valueBranches hb) hd)]
  exact dispatch_ofRegion _ _ _

section Quotient

open Paper.Extension.Singleton (projection)
variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option backward.isDefEq.respectTransparency false in
private theorem copair_map_congr {A B D : τ}
    {f f' : ofType (Φ := Φ) A ⟶ ofType D} {g g' : ofType (Φ := Φ) B ⟶ ofType D}
    (ef : (projection Seed).map f = (projection Seed).map f')
    (eg : (projection Seed).map g = (projection Seed).map g') :
    (projection Seed).map ((sumIso A B).hom ≫ coprod.desc f g) =
      (projection Seed).map ((sumIso A B).hom ≫ coprod.desc f' g') := by
  obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
  obtain ⟨_, hf', rfl⟩ := exists_ofRegion f'
  obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
  obtain ⟨_, hg', rfl⟩ := exists_ofRegion g'
  rw [coprod_desc_ofRegion, coprod_desc_ofRegion]
  have left := (Paper.Extension.Singleton.ofRegion_eq_iff Seed hf hf').1 ef
  have right := (Paper.Extension.Singleton.ofRegion_eq_iff Seed hg hg').1 eg
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (.case (.var (i := 0) rfl)
      (left.renameVars ((Ren.wk [] (Silmaril.coprod A B)).lift A))
      (right.renameVars ((Ren.wk [] (Silmaril.coprod A B)).lift B)))

set_option backward.isDefEq.respectTransparency false in
theorem canonicalAssembly_map_congr {X S D : τ}
    {e e' : ofType (Φ := Φ) X ⟶ ofType (packedExitType [S, D])}
    {b b' : ofType (Φ := Φ) (Silmaril.product X S) ⟶
      ofType (Silmaril.product X D) ⨿ ofType (Silmaril.product X S)}
    (ee : (projection Seed).map e = (projection Seed).map e')
    (eb : (projection Seed).map b = (projection Seed).map b') :
    (projection Seed).map (canonicalAssembly e b) = (projection Seed).map (canonicalAssembly e' b') := by
  have exitEq : (projection Seed).map (e ≫ exitSumArrow S D) =
      (projection Seed).map (e' ≫ exitSumArrow S D) := by simp only [Functor.map_comp, ee]
  have retainedEq := congrArg ((Paper.Extension.Singleton.whiskerLeftFunctor Seed
    ((projection Seed).obj (ofType (Φ := Φ) X))).map) exitEq
  rw [Paper.Extension.Singleton.whiskerLeft_map, Paper.Extension.Singleton.whiskerLeft_map] at retainedEq
  let drop := ofRegion (τ := τ) (productSndBranches (Φ := Φ) X D)
  have loopEq : (projection Seed).map (Paper.TypeCategory.iterate b ≫ drop) =
      (projection Seed).map (Paper.TypeCategory.iterate b' ≫ drop) := by
    simp only [Functor.map_comp, Paper.Extension.Singleton.iterate_map_congr Seed eb]
  have tailEq := copair_map_congr Seed (A := Silmaril.product X D) (B := Silmaril.product X S)
    (D := D) (f := drop) (f' := drop) rfl loopEq
  have factor (f : ofType (Φ := Φ) X ⟶ ofType (Silmaril.coprod D S))
      (g : ofType (Φ := Φ) (Silmaril.product X S) ⟶ ofType D) :
      (projection Seed).map (dispatchArrow f drop g) =
        (projection Seed).map ((ofRegion (τ := τ) (Paper.RetainedLet.diagonal_typed X) ≫
          whiskerLeft (ofType X) f) ≫ ofRegion (τ := τ) (CfgEta.TypeCategory.Retained.distributorRegion_typed X D S)) ≫
          (projection Seed).map ((sumIso (Silmaril.product X D) (Silmaril.product X S)).hom ≫ coprod.desc drop g) := by
    unfold dispatchArrow
    rw [← Category.assoc, ← Functor.map_comp]
  change (projection Seed).map (dispatchArrow _ drop _) = (projection Seed).map (dispatchArrow _ drop _)
  rw [factor, factor, tailEq]
  simp only [Functor.map_comp, retainedEq]
  rfl

end Quotient

section StepFactor

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  (J : V ⥤ Comp) [DistributiveFreydCategory J]
  (M : TypeModel τ V) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {X S D : τ}

set_option backward.isDefEq.respectTransparency false in
private theorem capturePrefix_factor (X S : τ) :
    let E := ctxObj M [X]
    let P := product X S
    (paperCarrier J M objIso X S).inv ≫
      retainEnvironment J (fst E (labelObj M [S])) (J.map (carriedIso M X S).hom) ≫
      J.map ((λ_ (M.obj X)).hom ▷ M.obj P) ≫ J.map (M.productIso X P).inv ≫
      (objIso (product X P)).hom = capturePrefix J M objIso X S := by
  dsimp only [paperCarrier, Iso.trans_inv, Functor.mapIso_inv, ctxObj]
  rw [Category.assoc, retainEnvironment_pre_assoc J, ← J.map_comp, Iso.inv_hom_id, retainEnvironment_map]
  simp only [capturePrefix, reindexHom, packedPair, ← J.map_comp_assoc]
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
theorem carriedStep_factor
    (whisker : ∀ {Y A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)),
      reindexHom J M objIso (J.map (M.productIso Y A).hom ≫ retainLeft J (R := M.obj Y) f ≫
        J.map (M.productIso Y B).inv) =
        whiskerLeft (ofType (Φ := Φ) Y) (reindexHom J M objIso f))
    (b : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    carriedStep J M objIso X S D b =
      capturePrefix J M objIso X S ≫ whiskerLeft (ofType X) (reindexHom J M objIso b) ≫
        carriedRoute J M objIso X S D := by
  let E := ctxObj M [X]
  let P := product X S
  let K := packedExitType [S, D]
  let kIso : E ≅ M.obj X := λ_ (M.obj X)
  let intro := J.map (carriedIso M X S).hom
  let split := J.map (unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D])
  let state := paperCarrier J M objIso X S
  let result := paperCarrier J M objIso X D
  change state.inv ≫ contextualStep J (intro ≫ b ≫ split) ≫ coprod.map result.hom state.hom = _
  have prefixEq := capturePrefix_factor J M objIso X S
  change state.inv ≫ retainEnvironment J (fst E (labelObj M [S])) intro ≫
    J.map (kIso.hom ▷ M.obj P) ≫ J.map (M.productIso X P).inv ≫
      (objIso (product X P)).hom = _ at prefixEq
  rw [contextualStep, ← Category.assoc intro b split, retainEnvironment_comp, retainEnvironment_comp,
    ← prefixEq, ← whisker (Y := X) (A := P) (B := K) b]
  change _ = _ ≫ _ ≫ ((objIso (product X K)).inv ≫ J.map (M.productIso X K).hom ≫
    J.map (kIso.inv ▷ M.obj K) ≫ retainLeft J (R := E) split ≫
    routeEnvironment J E (labelObj M [D]) (labelObj M [S]) ≫ coprod.map result.hom state.hom)
  simp only [reindexHom, Category.assoc, Iso.hom_inv_id_assoc, ← J.map_comp_assoc,
    Iso.inv_hom_id, Category.comp_id]
  simp only [Iso.inv_hom_id_assoc]
  rw [retainLeft_pre_map_assoc J kIso.hom b, ← J.map_comp_assoc,
    ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id, MonoidalCategory.id_whiskerRight,
    J.map_id, Category.id_comp]

end StepFactor

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp]
  [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]

/-- The retained iteration law only concerns the carried body before dropping the capture. -/
theorem contextualLoop_compare {E S D : V} (body : J.obj (E ⊗ S) ⟶ J.obj (D ⨿ S))
    {S' D' : Comp} (state : J.obj (E ⊗ S) ≅ S') (result : J.obj (E ⊗ D) ≅ D')
    (preserves : PreservesLoop (contextualStep J body)) :
    state.inv ≫ contextualLoop J body =
      Paper.TypeCategory.iterate (reindexStep state result (contextualStep J body)) ≫
        result.inv ≫ J.map (CartesianMonoidalCategory.snd E D) := by
  have h : contextualLoop J body =
      CategoryTheory.iterate (contextualStep J body) ≫ J.map (snd E D) := by
    simp only [contextualLoop, contextualStep, retainEnvironment, retainLeft, routeEnvironment,
      Category.assoc]
  unfold PreservesLoop at preserves
  rw [h, preserves, ← canonical_reindex]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem route_map {E A B A' B' : V} (l : A ⟶ A') (r : B ⟶ B') :
    J.map (E ◁ coprod.map l r) ≫ routeEnvironment J E A' B' =
      routeEnvironment J E A B ≫ coprod.map (J.map (E ◁ l)) (J.map (E ◁ r)) := by
  let route := routeEnvironment J E A B
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
    rw [← route_inl J, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hr : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [← route_inr J, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (inv route)).mp
  change inv route ≫ _ = inv route ≫ route ≫ _
  rw [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_map, reassoc_of% hl, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, coprod.inl_map, MonoidalCategory.whiskerLeft_comp,
      J.map_comp_assoc, route_inl J]
  · rw [coprod.inr_map, reassoc_of% hr, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, coprod.inr_map, MonoidalCategory.whiskerLeft_comp,
      J.map_comp_assoc, route_inr J]

set_option backward.isDefEq.respectTransparency false in
private theorem case_map {E A B A' B' : V} {Y : V} (f : J.obj E ⟶ J.obj (A ⨿ B))
    (l : A ⟶ A') (r : B ⟶ B')
    (g : J.obj (E ⊗ A') ⟶ J.obj Y) (h : J.obj (E ⊗ B') ⟶ J.obj Y) :
    caseWithContext J (f ≫ J.map (coprod.map l r)) g h =
      caseWithContext J f (J.map (E ◁ l) ≫ g) (J.map (E ◁ r) ≫ h) := by
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    ← Category.assoc (J.map (DistributiveTensor.leftIso _ _ _).inv)]
  change extend J (f ≫ J.map (coprod.map l r)) ≫ (routeEnvironment J E A' B' ≫ coprod.desc g h) = _
  rw [extend_postmap, Category.assoc, ← Category.assoc (J.map (E ◁ coprod.map l r)),
    route_map J l r, Category.assoc, coprod.map_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem case_labels {E A B A' B' Y : V} (f : J.obj E ⟶ J.obj (A ⨿ B))
    (left : A ≅ A') (right : B ≅ B') (g : J.obj (E ⊗ A) ⟶ J.obj Y) (h : J.obj (E ⊗ B) ⟶ J.obj Y) :
    caseWithContext J f g h =
      caseWithContext J (f ≫ J.map (coprod.map left.hom right.hom))
        (J.map (E ◁ left.inv) ≫ g) (J.map (E ◁ right.inv) ≫ h) := by
  rw [case_map]
  simp only [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]

private theorem case_postmap {E A B D Y : V} (f : J.obj E ⟶ J.obj (A ⨿ B))
    (g : J.obj (E ⊗ A) ⟶ J.obj D) (h : J.obj (E ⊗ B) ⟶ J.obj D) (k : J.obj D ⟶ J.obj Y) :
    caseWithContext J f g h ≫ k = caseWithContext J f (g ≫ k) (h ≫ k) := by
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Category.assoc, coprod.desc_comp]

variable (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem dispatch_compare (cmp : ModelComparisons J M objIso pe) {X A B D : τ}
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D)) :
    reindexHom J M objIso (caseWithContext J
      (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h)) =
      dispatchArrow (reindexHom J M objIso f)
        (reindexHom J M objIso g) (reindexHom J M objIso h) :=
  SingletonReification.factor_dispatch J M objIso pe cmp f g h

set_option backward.isDefEq.respectTransparency false in
omit [InstructionModel J M Φ] [SymmetricCategory V] [DistributiveTensor V] in
private theorem carried_drop (X D : τ) :
    (carriedIso M X D).inv ≫ snd (ctxObj M [X]) (labelObj M [D]) ≫
      singletonLabelPayload M D = sndMap M X D := by
  simp only [carriedIso, labelPayloadIso, sndMap, Iso.trans_inv,
    MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv, Iso.symm_inv,
    Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd_assoc]
  rw [labelInject_payload M D, Category.comp_id]
  change (M.productIso X D).hom ≫ (λ_ (M.obj X)).inv ▷ M.obj D ≫
    snd ((𝟙_ V) ⊗ M.obj X) (M.obj D) = _
  rw [CartesianMonoidalCategory.whiskerRight_snd]

set_option backward.isDefEq.respectTransparency false in
omit [InstructionModel J M Φ] in
theorem assemble_dispatch {X S D : τ}
    (e : J.obj (M.obj X) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (b : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    assemble J M X S D (Silmaril.product X S)
      (((λ_ (M.obj X)).hom ▷ M.obj S) ≫ (M.productIso X S).inv) e b =
    caseWithContext J ((e ≫ J.map (exitSum M S D)) ≫ J.map (M.coprodIso D S).hom)
      (J.map (M.productIso X D).inv ≫ J.map (sndMap M X D))
      (J.map (M.productIso X S).inv ≫
        J.map (carriedIso M X S).inv ≫ contextualLoop J (blockComputation M J X S D b) ≫
          J.map (singletonLabelPayload M D)) := by
  dsimp only [assemble]
  rw [← Category.assoc (J.map ((λ_ (M.obj X)).inv)),
    ← case_pre_map J ((λ_ (M.obj X)).inv), case_postmap,
    case_labels J _ (labelPayloadIso M D) (labelPayloadIso M S)]
  simp only [Category.assoc, ← J.map_comp_assoc, ← J.map_comp, Iso.inv_hom_id, J.map_id,
    Category.id_comp, Category.comp_id, exitSum, labelPayloadIso]
  congr 1
  · change J.map ((M.obj X ◁ labelInject M 0 rfl) ≫
        (λ_ (M.obj X)).inv ▷ labelObj M [D] ≫ snd ((𝟙_ V) ⊗ M.obj X) (labelObj M [D]) ≫
        singletonLabelPayload M D) = _
    simp only [sndMap, Iso.inv_hom_id_assoc,
      CartesianMonoidalCategory.whiskerRight_snd_assoc, CartesianMonoidalCategory.whiskerLeft_snd_assoc]
    rw [labelInject_payload M D, Category.comp_id]
  · dsimp only [blockComputation, carriedIso, labelPayloadIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, Iso.symm_hom, MonoidalCategory.whiskerLeftIso_hom, MonoidalCategory.whiskerRightIso_hom,
      MonoidalCategory.whiskerLeftIso_inv, MonoidalCategory.whiskerRightIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [MonoidalCategory.whisker_exchange]
    rfl

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc] private theorem exitSum_inl (S D : τ) :
    inlMap M S (Silmaril.coprod D Silmaril.empty) ≫ exitSum M S D = inrMap M D S := by
  simp only [exitSum, packedExitType, inlMap, inrMap, unpackLabel, Category.assoc,
    Iso.inv_hom_id_assoc, coprod.inl_desc_assoc, labelAppendSplit_zero_assoc,
    coprod.inr_map_assoc]
  rw [reassoc_of% (labelInject_payload M S)]

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc] private theorem exitSum_inr_inl (S D : τ) :
    inlMap M D Silmaril.empty ≫ inrMap M S (Silmaril.coprod D Silmaril.empty) ≫ exitSum M S D =
      inlMap M D S := by
  simp only [exitSum, packedExitType, inlMap, inrMap, unpackLabel, Category.assoc,
    Iso.inv_hom_id_assoc, coprod.inr_desc_assoc, coprod.inl_desc_assoc, labelInject_labelMap_assoc,
    labelAppendSplit_succ_assoc, coprod.inl_map_assoc]
  rw [reassoc_of% (labelInject_payload M D)]

set_option backward.isDefEq.respectTransparency false in
theorem exitSum_compare (cmp : ModelComparisons J M objIso pe) (S D : τ) :
    reindexHom J M objIso (J.map (exitSum M S D)) = exitSumArrow (Φ := Φ) S D := by
  have transport {A B C : τ} (f : M.obj A ⟶ M.obj B) (g : M.obj B ⟶ M.obj C) :
      reindexHom J M objIso (J.map f) ≫ reindexHom J M objIso (J.map g) =
        reindexHom J M objIso (J.map (f ≫ g)) := by simp [reindexHom]
  let g := (sumCofan (Φ := Φ) D S).inr
  let h := (sumCofan (Φ := Φ) D S).inl
  let z := ofRegion (τ := τ) (Φ := Φ) (emptyExit_typed (Silmaril.coprod D S))
  let tail := (sumIso D (Silmaril.empty : τ)).hom ≫ coprod.desc h z
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit S (Silmaril.coprod D Silmaril.empty))
  · have e := congrArg (fun f => reindexHom J M objIso (J.map f)) (exitSum_inl M S D)
    rw [← transport, cmp.inl, cmp.inr] at e
    exact e.trans (exact_inl g tail).symm
  · suffices (sumCofan S (Silmaril.coprod D Silmaril.empty)).inr ≫
        reindexHom J M objIso (J.map (exitSum M S D)) = tail from
      this.trans (exact_inr g tail).symm
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit D (Silmaril.empty : τ))
    · have e := congrArg (fun f => reindexHom J M objIso (J.map f)) (exitSum_inr_inl M S D)
      rw [← transport, ← transport, cmp.inl, cmp.inr, cmp.inl] at e
      exact e.trans (exact_inl h z).symm
    · exact empty_unique _ _

set_option backward.isDefEq.respectTransparency false in
private theorem loop_arm_compare (cmp : ModelComparisons J M objIso pe) {X S D : τ}
    (b : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D b))) :
    reindexHom J M objIso (J.map (carriedIso M X S).inv ≫
        contextualLoop J (blockComputation M J X S D b) ≫ J.map (singletonLabelPayload M D)) =
      Paper.TypeCategory.iterate (carriedStep J M objIso X S D b) ≫
        ofRegion (τ := τ) (productSndBranches X D) := by
  have h := contextualLoop_compare J (blockComputation M J X S D b)
    (paperCarrier J M objIso X S) (paperCarrier J M objIso X D) choice
  change _ = Paper.TypeCategory.iterate (carriedStep J M objIso X S D b) ≫ _ at h
  have hk := congrArg (fun f => f ≫ J.map (singletonLabelPayload M D) ≫ (objIso D).hom) h
  simp only [paperCarrier, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at hk
  have hDrop := cmp.snd X D
  unfold reindexHom at hDrop ⊢
  rw [← hDrop]
  simpa only [Category.assoc, ← J.map_comp_assoc, carried_drop M X D] using hk

set_option backward.isDefEq.respectTransparency false in
theorem compare_assemble (cmp : ModelComparisons J M objIso pe) {X S D : τ}
    (e : J.obj (M.obj X) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (b : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D b))) :
    reindexHom J M objIso (assemble J M X S D (Silmaril.product X S)
        (((λ_ (M.obj X)).hom ▷ M.obj S) ≫ (M.productIso X S).inv) e b) =
      canonicalAssembly (reindexHom J M objIso e) (carriedStep J M objIso X S D b) := by
  have hTag : reindexHom J M objIso (e ≫ J.map (exitSum M S D)) =
      reindexHom J M objIso e ≫ exitSumArrow (Φ := Φ) S D := by
    rw [← exitSum_compare J M objIso pe cmp]
    simp [reindexHom]
  rw [assemble_dispatch, dispatch_compare J M objIso pe cmp, hTag, cmp.snd,
    loop_arm_compare J M objIso pe cmp b choice]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem carriedStep_map_congr (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {X S D : τ}
    {b b' : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))}
    (e : (Paper.Extension.Singleton.projection Seed).map (reindexHom J M objIso b) =
        (Paper.Extension.Singleton.projection Seed).map (reindexHom J M objIso b')) :
    (Paper.Extension.Singleton.projection Seed).map (carriedStep J M objIso X S D b) =
      (Paper.Extension.Singleton.projection Seed).map (carriedStep J M objIso X S D b') := by
  have h := congrArg ((Paper.Extension.Singleton.whiskerLeftFunctor Seed
    ((Paper.Extension.Singleton.projection Seed).obj (ofType (Φ := Φ) X))).map) e
  rw [Paper.Extension.Singleton.whiskerLeft_map, Paper.Extension.Singleton.whiskerLeft_map] at h
  simp only [carriedStep_factor J M objIso (fun f => cmp.whisker f), Functor.map_comp, h]

open Paper.Extension.Singleton (projection)

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

/-- Reindex the guarded CFG denotation to canonical singleton arrows using
preservation at its one carried iteration step. -/
theorem compare_guardedCfg {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType)))) :
    reindexHom J M objIso (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType) =
      canonicalAssembly (reindexHom J M objIso (denoteSingletonRegion J M he.hasType))
        (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) := by
  rw [denote_guardedCfg J M he hb]
  exact compare_assemble J M objIso pe cmp _ _ choice

set_option backward.isDefEq.respectTransparency false in
/-- Reify the guarded one-block denotation in the extension quotient from
the projected comparisons of its packed singleton entry and block. The
result is the explicit canonical region with a representative of the
carried step. -/
theorem reify_guardedCfg {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    ∃ (step : Region Φ) (hs : ValueBranches [Silmaril.product X S] step
        [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]),
      carriedStep J M objIso X S D ((objIso (Silmaril.product X S)).hom ≫
        ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
          ofRegion (τ := τ) hs ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom ∧
      (projection Seed).map (reindexHom J M objIso
        (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
        Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) := by
  let F := projection Seed
  let b' := (objIso (Silmaril.product X S)).hom ≫ ofRegion (τ := τ) hb ≫
    (objIso (packedExitType [S, D])).inv
  have hBlock : reindexHom J M objIso b' = ofRegion (τ := τ) hb := by
    simp [b', reindexHom]
  have hStep := carriedStep_map_congr J M objIso pe cmp Seed
    (blockIH.trans (congrArg F.map hBlock).symm)
  let carried := carriedStep J M objIso X S D b'
  let tag := sumIso (Φ := Φ) (Silmaril.product X D) (Silmaril.product X S)
  obtain ⟨step, hs, h⟩ := exists_ofRegion (carried ≫ tag.inv)
  have hRepresentation : carried = ofRegion (τ := τ) hs ≫ tag.hom := by
    rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨step, hs, hRepresentation, ?_⟩
  rw [compare_guardedCfg J M objIso pe cmp he hb choice]
  apply (canonicalAssembly_map_congr Seed entryIH (hStep.trans (congrArg F.map hRepresentation))).trans
  exact congrArg F.map (canonicalAssembly_ofRegion he hs)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly
