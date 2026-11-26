module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Projection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRetainedBlock
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration

/-! # The retained interpretation of carried constructor blocks -/

public section

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst lift)
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType ofRegion DiscardPreservingValueCategory DiscardPreservingReturn discardPreservingFan
    whiskerLeft sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (packedSwap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
  (blockComputation carriedIso retagPacked_typed realizePackedStep_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.Model (reindexHom carrier carriedRoute)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap)
open _root_.Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion_valueBranches)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Comp" => Paper.WithProjectionReturnsAndUnitEta.TypeCategory (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Obj" => ofType (Seed)
set_option hygiene false in
local notation "Lit" => ofRegion (Seed)
/-- The descended Paper iterator returns immediately on the chosen result injection. -/
theorem canonicalIterate_return {A B : τ} (f : Obj A ⟶ Obj B) :
    canonicalIterate (f ≫ coprod.inl) = f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration.canonicalIterate_return f

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

section Transport

variable (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The state isomorphism reindexes the step, and the output coproduct
isomorphism reindexes the result and repeat arms in that order. -/
theorem actualCarriedStep_carrier_square {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    (carrier J M objIso X S).hom ≫ actualCarriedStep J M objIso hb =
      contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) ≫
        coprod.map (carrier J M objIso X D).hom (carrier J M objIso X S).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration.actualCarriedStep_carrier_square J M objIso hb

/-- Both iterators reduce to the returned arrow when the actual step only takes
the result arm. -/
theorem transportedIterationAgrees_of_return {X S D : τ} {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (out : J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (ctxObj M [X] ⊗ labelObj M [D]))
    (step : contextualStep J (blockComputation M J X S D (denoteSingletonRegion J M hb.hasType)) =
      out ≫ coprod.inl) :
    TransportedIterationAgrees J M objIso hb :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration.transportedIterationAgrees_of_return
    J M objIso hb out step

end Transport

variable [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ Obj A)

/-- The actual capture-result step keeps the environment, returns its capture
field, and takes the result injection. -/
theorem captureResult_actualStep (X S : τ) :
    contextualStep J (blockComputation M J X S X
      (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType)) =
      J.map (lift (fst (ctxObj M [X]) (labelObj M [S]))
        ((carriedIso M X S).hom ≫ fstMap M X S ≫ labelInject M 0 (L := [X]) rfl)) ≫ coprod.inl :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration.captureResult_actualStep J M X S

/-- The actual and guarded iterators agree at the capture-result block by
their one-step return equations. -/
theorem captureResult_transportedIterationAgrees (X S : τ) :
    TransportedIterationAgrees J M objIso (captureResultBlock (Φ := Φ) X S) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCaptureIteration.captureResult_transportedIterationAgrees
    J M objIso X S

/-- The actual retained block adds the result tag to the interpreted constructor payload. -/
theorem retainedConstructorResult_eq {X S D : τ} {a : Tm Φ}
    (ha : Tm.BranchValue [S, X, product X S] a D)
    (payload : reindexHom J M objIso (denoteSingletonRegion J M (unpackedConstructorReturn ha).hasType) =
      Lit (unpackedConstructorReturn ha))
    (input : RetainedTensorAgrees J M objIso X (product X S))
    (output : RetainedPackedExitsAgree J M objIso X S D) :
    reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M (constructorResultBlock ha).hasType) ≫
      J.map (M.productIso X (packedExitType [S, D])).inv) =
        whiskerLeft (Seed) (Obj X) (Lit (constructorResultBlock ha)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRetainedBlock.retainedConstructorResult_eq
    J M objIso ha payload input output

/-- The actual block returning the capture field uses the guarded projection comparison. -/
theorem retainedCaptureResult_eq (X S : τ)
    (projection : reindexHom J M objIso (J.map (fstMap M X S)) = Lit (productFstBranches X S))
    (input : RetainedTensorAgrees J M objIso X (product X S))
    (output : RetainedPackedExitsAgree J M objIso X S X) :
    reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType) ≫
      J.map (M.productIso X (packedExitType [S, X])).inv) =
        whiskerLeft (Seed) (Obj X) (Lit (captureResultBlock X S)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRetainedBlock.retainedCaptureResult_eq
    J M objIso X S projection input output

/-- The actual block swapping both fields uses the untagged packed swap comparison. -/
theorem retainedSwapResult_eq (X S : τ)
    (swap : reindexHom J M objIso (J.map (packedSwap M X S)) = Lit (Paper.TypeCategory.braidBranches X S))
    (input : RetainedTensorAgrees J M objIso X (product X S))
    (output : RetainedPackedExitsAgree J M objIso X S (product S X)) :
    reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
      retainLeft J (R := M.obj X) (denoteSingletonRegion J M (swapResultBlock (Φ := Φ) X S).hasType) ≫
      J.map (M.productIso X (packedExitType [S, product S X])).inv) =
        whiskerLeft (Seed) (Obj X) (Lit (swapResultBlock X S)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedRetainedBlock.retainedSwapResult_eq
    J M objIso X S swap input output

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory (Seed) pe
set_option hygiene false in
local notation "Val" => fun (A : τ) => (⟨Obj A⟩ : Values)
set_option hygiene false in
local notation "I" => wideSubcategoryInclusion (DiscardPreservingReturn (Seed) pe)

set_option hygiene false in
local notation "fan" => discardPreservingFan (Seed) pe (fun h => Or.inl h)

/-- Reify the actual carried loop whose block destructures the input and returns
the captured field. The route and the transported iterator are compared separately. -/
theorem actualCarriedIteration_eq_captureResult (X S : τ)
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
    (retainedInput : RetainedTensorAgrees J M objIso X (product X S))
    (retainedOutput : RetainedPackedExitsAgree J M objIso X S X)
    (route : carriedRoute J M objIso X S X =
      Lit (retagPacked_typed X S X) ≫ (sumIso (Seed) (product X X) (product X S)).hom)
    (iteration : TransportedIterationAgrees J M objIso (captureResultBlock X S)) :
    let actual := contextualStep J (blockComputation M J X S X
      (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X X
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed (captureResultBlock X S))) :=
  actualCarriedIteration_eq_of_valueProjectionCoordinates pe J M objIso
    (hb := captureResultBlock X S) K q capture state captureCoord stateCoord firstLeg diagonalCoord blockInputCoord
    (retainedCaptureResult_eq J M objIso X S
      ((fst_eq_iff_value_product_leg pe K M J objIso X S q capture state.hom captureCoord stateCoord).2 firstLeg)
      retainedInput retainedOutput)
    route iteration

/-- Reify the actual carried loop whose block destructures the input and returns
the captured field. The two carrier product coordinates determine the route. -/
theorem actualCarriedIteration_eq_captureResult_of_carrierTensor (X S : τ)
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
    (retainedInput : RetainedTensorAgrees J M objIso X (product X S))
    (retainedOutput : RetainedPackedExitsAgree J M objIso X S X)
    (stateCarrier : RetainedTensorAgrees J M objIso X S)
    (resultCarrier : RetainedTensorAgrees J M objIso X X)
    (iteration : TransportedIterationAgrees J M objIso (captureResultBlock X S)) :
    let actual := contextualStep J (blockComputation M J X S X
      (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X X
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed (captureResultBlock X S))) :=
  actualCarriedIteration_eq_captureResult J M objIso pe X S K q capture state captureCoord stateCoord
    firstLeg diagonalCoord blockInputCoord retainedInput retainedOutput
    (carriedRoute_eq_of_carrierTensor J M objIso X S X stateCarrier resultCarrier retainedOutput) iteration

/-- Reify the capture-result loop using its carrier product coordinates and
the computed one-step return. -/
theorem actualCarriedIteration_eq_captureResult_of_coordinates (X S : τ)
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
    (retainedInput : RetainedTensorAgrees J M objIso X (product X S))
    (retainedOutput : RetainedPackedExitsAgree J M objIso X S X)
    (stateCarrier : RetainedTensorAgrees J M objIso X S)
    (resultCarrier : RetainedTensorAgrees J M objIso X X) :
    let actual := contextualStep J (blockComputation M J X S X
      (denoteSingletonRegion J M (captureResultBlock (Φ := Φ) X S).hasType))
    let state := carrier J M objIso X S
    let result := carrier J M objIso X X
    state.inv ≫ CategoryTheory.iterate actual ≫ result.hom =
      Lit (iterateRegion_valueBranches (realizePackedStep_typed (captureResultBlock X S))) :=
  actualCarriedIteration_eq_captureResult_of_carrierTensor J M objIso pe X S K q capture state
    captureCoord stateCoord firstLeg diagonalCoord blockInputCoord retainedInput retainedOutput
    stateCarrier resultCarrier (captureResult_transportedIterationAgrees J M objIso X S)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
