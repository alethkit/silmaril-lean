module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Diagonal.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection

/-! # Carried first projection and right whisker from value product coordinates -/

public section

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType ofRegion DiscardPreservingValueCategory DiscardPreservingReturn discardPreservingFan
    discardPreservingBinaryFanIsLimit productFst whiskerLeft whiskerRight sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (packedWhiskerRight)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
  (blockComputation retagPacked_typed realizePackedStep_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model (reindexHom carrier carriedRoute)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (fstTerm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)
set_option hygiene false in
local notation "Lit" => ofRegion (Seed)
set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory (Seed) pe
set_option hygiene false in
local notation "Val" => fun (A : τ) => (⟨Obj A⟩ : Values)
set_option hygiene false in
local notation "I" => wideSubcategoryInclusion (DiscardPreservingReturn (Seed) pe)

set_option hygiene false in
local notation "fan" => discardPreservingFan (Seed) pe (fun h => Or.inl h)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

section Coordinates

variable (K : V ⥤ Values) (M : TypeModel τ V)
  (J : V ⥤ Comp) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The first leg of the induced binary product map is the interpreted first projection. -/
theorem chosenBinaryValueProductMap_fst (A B : τ)
    (a : K.obj (M.obj A) ≅ Val A) (b : K.obj (M.obj B) ≅ Val B) :
    chosenBinaryValueProductMap pe K M A B a b ≫ ((fan) A B).fst = K.map (fstMap M A B) ≫ a.hom :=
  BinaryFan.IsLimit.lift_fst (discardPreservingBinaryFanIsLimit (Seed) pe A B (fun h => Or.inl h)) _ _

/-- Naturality and faithfulness transport a value square through two local object coordinates. -/
theorem reindex_eq_iff_value_square {A B : τ} (f : M.obj A ⟶ M.obj B)
    (q : K ⋙ (I) ≅ J)
    (a : K.obj (M.obj A) ⟶ Val A) (b : K.obj (M.obj B) ⟶ Val B) (g : Val A ⟶ Val B)
    (source : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map a)
    (target : (objIso B).hom = (q.app (M.obj B)).inv ≫ (I).map b) :
    reindexHom J M objIso (J.map f) = (I).map g ↔ K.map f ≫ b = a ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection.reindex_eq_iff_value_square
    pe K M J objIso f q a b g source target

/-- The exact first-leg condition at the selected product coordinate. -/
theorem fst_eq_iff_value_product_leg (A B : τ) (q : K ⋙ (I) ≅ J)
    (e : K.obj (M.obj A) ≅ Val A) (p : K.obj (M.obj (product A B)) ⟶ Val (product A B))
    (first : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map e.hom)
    (productCoord : (objIso (product A B)).hom = (q.app (M.obj (product A B))).inv ≫ (I).map p) :
    reindexHom J M objIso (J.map (fstMap M A B)) = productFst (Seed) A B ↔
      p ≫ ((fan) A B).fst = K.map (fstMap M A B) ≫ e.hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection.fst_eq_iff_value_product_leg
    pe K M J objIso A B q e p first productCoord

/-- With the source product coordinate fixed, the right-whisker comparison
tests the target product coordinate only after the interpreted packed whisker. -/
theorem reindexPackedWhiskerRight_eq_iff_targetProduct {A B R : τ} (f : M.obj A ⟶ M.obj B)
    (q : K ⋙ (I) ≅ J)
    (a : K.obj (M.obj A) ≅ Val A) (b : K.obj (M.obj B) ≅ Val B) (r : K.obj (M.obj R) ≅ Val R)
    (src : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map a.hom)
    (dst : (objIso B).hom = (q.app (M.obj B)).inv ≫ (I).map b.hom)
    (sourceProduct : (objIso (product A R)).hom =
      (q.app (M.obj (product A R))).inv ≫ (I).map (chosenBinaryValueProductMap pe K M A R a r)) :
    (reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
      whiskerRight (Seed) (reindexHom J M objIso (J.map f)) (Obj R)) ↔
    J.map (packedWhiskerRight M R A B f) ≫ (objIso (product B R)).hom =
      J.map (packedWhiskerRight M R A B f) ≫ (q.app (M.obj (product B R))).inv ≫
        (I).map (chosenBinaryValueProductMap pe K M B R b r) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection.reindexPackedWhiskerRight_eq_iff_targetProduct
    pe K M J objIso f q a b r src dst sourceProduct

/-- Right whiskering commutes with interpretation at the two induced product coordinates. -/
theorem reindexPackedWhiskerRight_of_valueProductMaps {A B R : τ} (f : M.obj A ⟶ M.obj B)
    (q : K ⋙ (I) ≅ J)
    (a : K.obj (M.obj A) ≅ Val A) (b : K.obj (M.obj B) ≅ Val B) (r : K.obj (M.obj R) ≅ Val R)
    (src : (objIso A).hom = (q.app (M.obj A)).inv ≫ (I).map a.hom)
    (dst : (objIso B).hom = (q.app (M.obj B)).inv ≫ (I).map b.hom)
    (sourceProduct : (objIso (product A R)).hom =
      (q.app (M.obj (product A R))).inv ≫ (I).map (chosenBinaryValueProductMap pe K M A R a r))
    (targetProduct : (objIso (product B R)).hom =
      (q.app (M.obj (product B R))).inv ≫ (I).map (chosenBinaryValueProductMap pe K M B R b r)) :
    reindexHom J M objIso (J.map (packedWhiskerRight M R A B f)) =
      whiskerRight (Seed) (reindexHom J M objIso (J.map f)) (Obj R) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedProjection.reindexPackedWhiskerRight_of_valueProductMaps
    pe K M J objIso f q a b r src dst sourceProduct targetProduct

end Coordinates

section Carried

variable [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The first-leg comparison also identifies the actual return-region denotation. -/
theorem fstProducer_denote_of_valueProductLeg [RegionTypingCoherent (Φ := Φ) J M] (X S : τ)
    (K : V ⥤ Values) (q : K ⋙ (I) ≅ J)
    (e : K.obj (M.obj X) ≅ Val X) (p : K.obj (M.obj (product X S)) ⟶ Val (product X S))
    (first : (objIso X).hom = (q.app (M.obj X)).inv ≫ (I).map e.hom)
    (productCoord : (objIso (product X S)).hom = (q.app (M.obj (product X S))).inv ≫ (I).map p)
    (firstLeg : p ≫ ((fan) X S).fst = K.map (fstMap M X S) ≫ e.hom) :
    reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) X S)).hasType) =
      Lit (returnOnce_typed (fstTerm X S)) :=
  (fstProducer_denote_iff J M objIso X S).2
    ((fst_eq_iff_value_product_leg pe K M J objIso X S q e p first productCoord).2 firstLeg)

/-- Reify the actual transported iteration with its capture prefix supplied
by the chosen diagonal, first projection and right whisker on values. -/
theorem actualCarriedIteration_eq_of_valueProjectionCoordinates {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (K : V ⥤ Values) (q : K ⋙ (I) ≅ J)
    (capture : K.obj (M.obj X) ≅ Val X)
    (state : K.obj (M.obj (product X S)) ≅ Val (product X S))
    (captureCoord : (objIso X).hom = (q.app (M.obj X)).inv ≫ (I).map capture.hom)
    (stateCoord : let P := product X S
      (objIso P).hom = (q.app (M.obj P)).inv ≫ (I).map state.hom)
    (firstLeg : state.hom ≫ ((fan) X S).fst = K.map (fstMap M X S) ≫ capture.hom)
    (diagonalCoord : let P := product X S
      (objIso (product P P)).hom =
        (q.app (M.obj (product P P))).inv ≫ (I).map (chosenValueProductMap pe K M P state))
    (blockInputCoord : let P := product X S
      (objIso (product X P)).hom =
        (q.app (M.obj (product X P))).inv ≫
          (I).map (chosenBinaryValueProductMap pe K M X P capture state))
    (block : let P := product X S
      let K := packedExitType [S, D]
      reindexHom J M objIso (J.map (M.productIso X P).hom ≫
        retainLeft J (R := M.obj X) (denoteSingletonRegion J M hb.hasType) ≫
          J.map (M.productIso X K).inv) = whiskerLeft (Seed) (Obj X) (Lit hb))
    (route : carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom)
    (iteration : TransportedIterationAgrees J M objIso hb) :
    let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X D
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed hb)) :=
  actualCarriedIteration_eq_of_valueProductMap pe J M objIso K state q stateCoord diagonalCoord
    ((fst_eq_iff_value_product_leg pe K M J objIso X S q capture state.hom captureCoord stateCoord).2 firstLeg)
    (reindexPackedWhiskerRight_of_valueProductMaps pe K M J objIso (fstMap M X S) q state capture state
      stateCoord captureCoord diagonalCoord blockInputCoord)
    block route iteration

end Carried

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
