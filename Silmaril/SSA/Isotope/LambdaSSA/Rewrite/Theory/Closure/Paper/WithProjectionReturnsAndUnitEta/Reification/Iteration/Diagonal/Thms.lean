module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Diagonal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal

/-! # The actual carried diagonal from product comparisons on values -/

public section

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType ofRegion DiscardPreservingValueCategory DiscardPreservingReturn discardPreservingFan ProjectedCopyingReturn
    diagonalArrow productFst productSnd whiskerLeft whiskerRight sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (packedDiagonal packedWhiskerRight)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
  (blockComputation retagPacked_typed realizePackedStep_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model (reindexHom carrier carriedRoute)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap sndMap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
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

/-- The value product diagonal includes as the guarded constructor return. -/
theorem chosenValueDiagonal_map (P : τ) :
    (I).map (chosenValueDiagonal (Φ := Φ) pe P) = diagonalArrow (Seed) (Obj P) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal.chosenValueDiagonal_map pe P

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

section ValueMap

variable (K : V ⥤ Values) (M : TypeModel τ V)

/-- A proposed value product coordinate is the chosen map exactly when its
two legs are the interpreted packed projections. -/
theorem eq_chosenValueProductMap_iff (P : τ) (e : K.obj (M.obj P) ≅ Val P)
    (p : K.obj (M.obj (product P P)) ⟶ Val (product P P)) :
    p = chosenValueProductMap pe K M P e ↔
      p ≫ (discardPreservingFan (Seed) pe (fun h => Or.inl h) P P).fst = K.map (fstMap M P P) ≫ e.hom ∧
      p ≫ (discardPreservingFan (Seed) pe (fun h => Or.inl h) P P).snd = K.map (sndMap M P P) ≫ e.hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal.eq_chosenValueProductMap_iff
    pe K M P e p

/-- In the certified value category, the interpreted duplicate has both identity
projections after using the product map induced by the chosen fan. -/
theorem reindexDiagonal_chosenValueProductMap (P : τ) (e : K.obj (M.obj P) ≅ Val P) :
    e.inv ≫ K.map (packedDiagonal M P) ≫ chosenValueProductMap pe K M P e =
      chosenValueDiagonal pe P :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal.reindexDiagonal_chosenValueProductMap pe K M P e

variable (J : V ⥤ Comp) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- For a value interpretation factoring the computation model, the input
coordinate lifts to values and the product coordinate is compared to the
chosen map. Those two coordinates give the carried diagonal. -/
theorem diagonal_eq_of_valueProductMap (P : τ) (e : K.obj (M.obj P) ≅ Val P)
    (q : K ⋙ (I) ≅ J)
    (source : (objIso P).hom = (q.app (M.obj P)).inv ≫ (I).map e.hom)
    (target : (objIso (product P P)).hom =
      (q.app (M.obj (product P P))).inv ≫ (I).map (chosenValueProductMap pe K M P e)) :
    reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal.diagonal_eq_of_valueProductMap pe K M J objIso P e q source target

end ValueMap

section Local

variable (J : V ⥤ Comp) (M : TypeModel τ V) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- Once the two packed projections agree, the residual is membership of the
reindexed duplicate in the projected copying values. Its discard equation
follows already from the first projection. -/
theorem diagonal_eq_iff_projectedCopying (P : τ)
    (fstAgrees : reindexHom J M objIso (J.map (fstMap M P P)) = productFst (Seed) P P)
    (sndAgrees : reindexHom J M objIso (J.map (sndMap M P P)) = productSnd (Seed) P P) :
    reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P) ↔
      ProjectedCopyingReturn (Seed) pe (reindexHom J M objIso (J.map (packedDiagonal M P))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCarriedDiagonal.diagonal_eq_iff_projectedCopying pe M J objIso P fstAgrees sndAgrees

end Local

section Carried

variable [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- Reify the actual transported iteration with the diagonal supplied by
the interpreted value product coordinates. -/
theorem actualCarriedIteration_eq_of_valueProductMap {X S D : τ} {b : Region Φ}
    {hb : ValueBranches [product X S] b [packedExitType [S, D]]}
    (K : V ⥤ Values)
    (e : K.obj (M.obj (product X S)) ≅ Val (product X S)) (q : K ⋙ (I) ≅ J)
    (source : let P := product X S
      (objIso P).hom = (q.app (M.obj P)).inv ≫ (I).map e.hom)
    (target : let P := product X S
      (objIso (product P P)).hom =
        (q.app (M.obj (product P P))).inv ≫ (I).map (chosenValueProductMap pe K M P e))
    (fstProducer :
      reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S))
    (fstWhisker : let P := product X S
      reindexHom J M objIso (J.map (packedWhiskerRight M P P X (fstMap M X S))) =
        whiskerRight (Seed) (reindexHom J M objIso (J.map (fstMap M X S))) (Obj P))
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
  actualCarriedIteration_eq J M objIso
    ⟨fstProducer, diagonal_eq_of_valueProductMap pe K M J objIso (product X S) e q source target,
      fstWhisker, block, route⟩ iteration

end Carried

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
