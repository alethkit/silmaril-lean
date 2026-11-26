module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Factor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
public import Mathlib.Data.Quot

/-! # Actual carried steps in the projection-return and unit-η singleton quotient -/

@[expose] public section

universe u v u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (packedDiagonal packedWhiskerRight)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg (retagPacked_typed blockComputation)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap inlMap inrMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Seed)
set_option hygiene false in
local notation "Lit" => Paper.Extension.Singleton.ofRegion (Seed)
set_option hygiene false in
local notation "F" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := τ) (Φ := Φ)

scoped instance computationPremonoidal : PremonoidalCategory Comp :=
  premonoidalOfUnitEta (Seed) (fun h => Or.inr h)

scoped instance computationSymmetricPremonoidal : SymmetricPremonoidalCategory Comp :=
  symmetricPremonoidalOfUnitEta (Seed) (fun h => Or.inr h)

/-- Run the descended guarded iterator on a step given at the chosen coproduct. -/
noncomputable def canonicalIterate {X Y : Comp} (step : X ⟶ Y ⨿ X) : X ⟶ Y :=
  iterateSum (Seed) (step ≫ (sumIso (Seed) (show τ from Y.as) (show τ from X.as)).inv)

/-- Assemble a packed entry and exact-sum carried step using the descended
canonical dispatcher and loop. Both inputs are already quotient arrows. -/
noncomputable def canonicalAssembly {X S D : τ}
    (entry : Obj X ⟶ Obj (packedExitType [S, D]))
    (step : Obj (product X S) ⟶ Obj (coprod (product X D) (product X S))) : Obj X ⟶ Obj D :=
  Quot.liftOn₂ entry step
    (fun e b => (F).map (Paper.SingletonReification.SingleCfg.canonicalAssembly e
      (b ≫ (Paper.TypeCategory.sumIso (product X D) (product X S)).hom)))
    (fun _ b b' h => by
      apply Paper.SingletonReification.SingleCfg.canonicalAssembly_map_congr (Seed) (X := X) (S := S) (D := D) rfl
      rw [Functor.map_comp, Functor.map_comp, show (F).map b = (F).map b' from Quot.sound h])
    (fun _ _ _ h => Paper.SingletonReification.SingleCfg.canonicalAssembly_map_congr (Seed)
      (X := X) (S := S) (D := D) (Quot.sound h) rfl)

section Route

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  (J : V ⥤ Comp) [DistributiveFreydCategory J] (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model
  (reindexHom packedTensorIso)

/-- The packed product comparison agrees with the two object isomorphisms
applied in the order used by left retention. -/
def RetainedTensorAgrees (X A : τ) : Prop :=
  (packedTensorIso J M objIso X A).hom =
    ((objIso X).hom ▷ J.obj (M.obj A)) ≫ (Obj X ◁ (objIso A).hom)

/-- The target's exact sum, with its coordinates determined by the two summands. -/
noncomputable def interpretedSumIso (A B : τ)
    (left : J.obj (M.obj A) ≅ Obj A) (right : J.obj (M.obj B) ≅ Obj B) :
    J.obj (M.obj (coprod A B)) ≅ Obj (coprod A B) :=
  J.mapIso (M.coprodIso A B) ≪≫ (asIso (coprodComparison J (M.obj A) (M.obj B))).symm ≪≫
    coprod.mapIso left right ≪≫ (sumIso (Seed) A B).symm

/-- The packed exits use the sum order `S + (D + empty)`. Their coordinates
are induced by the state, result, and empty isomorphisms. -/
noncomputable def packedExitIso (S D : τ) :
    J.obj (M.obj (packedExitType [S, D])) ≅ Obj (packedExitType [S, D]) :=
  interpretedSumIso J M S (coprod D Silmaril.empty) (objIso S)
    (interpretedSumIso J M D Silmaril.empty (objIso D) (objIso Silmaril.empty))

/-- The retained packed input uses the coordinate isomorphism determined by
the two exit tags. Only the coordinate of the full product is compared. -/
def RetainedPackedExitsAgree (X S D : τ) : Prop :=
  (packedTensorIso J M objIso X (packedExitType [S, D])).hom =
    ((objIso X).hom ▷ J.obj (M.obj (packedExitType [S, D]))) ≫
      (Obj X ◁ (packedExitIso J M objIso S D).hom)

/-- Both interpreted injections use the joined quotient's exact sum coordinates. -/
def SumInjectionsAgree (A B : τ) : Prop :=
  reindexHom J M objIso (J.map (inlMap M A B)) = (sumCofan (Seed) A B).inl ∧
  reindexHom J M objIso (J.map (inrMap M A B)) = (sumCofan (Seed) A B).inr

/-- The local sum and tensor comparisons that transport the carried distributor. -/
structure CarriedDistributorCoordinates (X S D : τ) : Prop where
  exitSum : SumInjectionsAgree J M objIso D S
  carriedSum : SumInjectionsAgree J M objIso (product X D) (product X S)
  tensorState : RetainedTensorAgrees J M objIso X S
  tensorResult : RetainedTensorAgrees J M objIso X D
  tensorExitSum : RetainedTensorAgrees J M objIso X (coprod D S)

end Route

section Model

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model (reindexHom carrier carriedStep carriedRoute)

/-- Reindex the actual denotation of the packed block as an ordinary carried computation step. -/
noncomputable def actualCarriedStep {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    Obj (product X S) ⟶ Obj (product X D) ⨿ Obj (product X S) :=
  carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)

/-- Compare the interpreted first projection, diagonal, retained projection,
retained actual block, and result routing at this one block's exact interface. -/
structure CarriedStepComparisons {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) : Prop where
  fstProducer :
    reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S)
  diagonal : let P := product X S
    reindexHom J M objIso (J.map (packedDiagonal M P)) = diagonalArrow (Seed) (Obj P)
  fstWhisker : let P := product X S
    reindexHom J M objIso (J.map (packedWhiskerRight M P P X (fstMap M X S))) =
      whiskerRight (Seed) (reindexHom J M objIso (J.map (fstMap M X S))) (Obj P)
  block : let P := product X S
    let K := packedExitType [S, D]
    reindexHom J M objIso (J.map (M.productIso X P).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M hb.hasType) ≫
        J.map (M.productIso X K).inv) = whiskerLeft (Seed) (Obj X) (Lit hb)
  route :
    carriedRoute J M objIso X S D =
      Lit (retagPacked_typed X S D) ≫ (sumIso (Seed) (product X D) (product X S)).hom

/-- The exact comparison needed to identify the transported model iterator with
the guarded iterator on this reindexed step. -/
def TransportedIterationAgrees {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) : Prop :=
  let actual := contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType))
  let state := carrier J M objIso X S
  let result := carrier J M objIso X D
  state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
    canonicalIterate (actualCarriedStep J M objIso hb)

end Model

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
