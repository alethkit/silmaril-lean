module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Reification.Thms

/-! # Local comparisons for the actual carried step in the projection-return quotient -/

@[expose] public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.TypeCategory (ofType ofRegion sumIso diagonalArrow whiskerRight whiskerLeft)
open Paper.RetainedLet (returnOnce_typed)
open Paper.RetainedCase (reindexHom)
open Paper.SingletonReification (packedDiagonal packedWhiskerRight reindexValueHom)
open Paper.SingletonReification.SingleCfg (retagPacked_typed carriedRoute)
open CfgEta.TypeCategory.ConstructorReification (fstMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
set_option hygiene false in
local notation "F" => WithProjectionReturns.projection (τ := τ) (Φ := Φ)

/-- A default Paper arrow built by copying the input and returning its first
projection as an expression on the first copy. -/
def captureViaReturn (X S : τ) : ofType (Φ := Φ) (product X S) ⟶ ofType (product X (product X S)) :=
  let P := product X S
  diagonalArrow P ≫ whiskerRight (ofRegion (returnOnce_typed (fstTerm X S))) (ofType P)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)

/-- Only five projected comparisons at this block's interface. The guarded
projection itself follows from the projection-return seed. The block field
compares the locally retained arrow, including its two product conversions. -/
structure CarriedStepComparisons {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) : Prop where
  fstProducer :
    (F).map (reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) X S)).hasType)) =
      (F).map (ofRegion (returnOnce_typed (fstTerm (Φ := Φ) X S)))
  diagonal : let P := product X S
    (F).map (reindexValueHom J M objIso P (product P P) (packedDiagonal M P)) =
      (F).map (diagonalArrow P)
  fstWhisker : let P := product X S
    (F).map (reindexValueHom J M objIso (product P P) (product X P)
      (packedWhiskerRight M P P X (fstMap M X S))) =
      (Paper.Extension.Singleton.whiskerRightFunctor Step ((F).obj (ofType P))).map
        ((F).map (reindexValueHom J M objIso P X (fstMap M X S)))
  block : let P := product X S
    let K := packedExitType [S, D]
    (F).map (reindexHom J M objIso (J.map (M.productIso X P).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M hb.hasType) ≫
      J.map (M.productIso X K).inv)) =
      (F).map (whiskerLeft (ofType X) (ofRegion hb))
  route :
    (F).map (carriedRoute J M objIso X S D) =
      (F).map (ofRegion (retagPacked_typed X S D) ≫ (sumIso (product X D) (product X S)).hom)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification
