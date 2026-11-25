module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # The dispatcher and retained feedback at separate interfaces -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open SingletonDispatcher (labelInject_payload payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Paper.TypeCategory
open Paper.RetainedLet (diagonal_typed)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open CfgEta.TypeCategory (caseValueBranches productSndBranches seqValueBranches)
open Paper.PackedBody (applyPacked_typed)
open Paper.RetainedCase (assembleCase_typed)
open SyntacticCategory (iterateRegion_valueBranches)
open Silmaril.Isotope.LetIter.Semantics.Categorical (contextualStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => TypeCategory (τ := τ) Φ

/-- The exact-sum dispatcher retains the input and distributes it to the selected arm. -/
noncomputable def dispatchArrow {X A B D : τ}
    (f : ofType (Φ := Φ) X ⟶ ofType (Silmaril.coprod A B))
    (g : ofType (Φ := Φ) (Silmaril.product X A) ⟶ ofType D)
    (h : ofType (Φ := Φ) (Silmaril.product X B) ⟶ ofType D) : ofType (Φ := Φ) X ⟶ ofType D :=
  (ofRegion (τ := τ) (diagonal_typed X) ≫ whiskerLeft (ofType X) f) ≫
    ofRegion (τ := τ) (distributorRegion_typed X A B) ≫
    (sumIso (Silmaril.product X A) (Silmaril.product X B)).hom ≫ coprod.desc g h

/-- Reindex a step with an independent comparison for its result and its carried state. -/
noncomputable def reindexStep {U V X Y : Comp}
    (state : U ≅ X) (result : V ≅ Y) (step : U ⟶ V ⨿ U) : X ⟶ Y ⨿ X :=
  state.inv ≫ step ≫ coprod.map result.hom state.hom

/-- Select the guarded Paper operation explicitly for a model. -/
noncomputable abbrev canonicalIteration [HasFiniteCoproducts Comp] : Iteration Comp where
  iterate := Paper.TypeCategory.iterate

/-- Local agreement with canonical Paper iteration at the actual carried step. -/
def PreservesLoop {U V : Comp} [HasFiniteCoproducts Comp] [Iteration Comp]
    (step : U ⟶ V ⨿ U) : Prop :=
  CategoryTheory.iterate step = Paper.TypeCategory.iterate step

/-- An impossible payload can feed back to itself at any outward type. -/
theorem emptyExit_typed (D : τ) :
    ValueBranches [Silmaril.empty] (unpackExits ([] : LCtx τ) : Region Φ) [D] :=
  .cfg (fun _ : Fin 1 => Silmaril.empty) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))

/-- Convert the packed list of two exits to the exact return-or-repeat sum. -/
noncomputable def exitSumArrow (S D : τ) :
    ofType (Φ := Φ) (packedExitType [S, D]) ⟶ ofType (Silmaril.coprod D S) :=
  (sumIso S (Silmaril.coprod D Silmaril.empty)).hom ≫ coprod.desc (sumCofan D S).inr
    ((sumIso D Silmaril.empty).hom ≫ coprod.desc (sumCofan D S).inl
      (ofRegion (τ := τ) (emptyExit_typed (Silmaril.coprod D S))))

/-- Run the packed entry and use canonical Paper iteration for the carried
state. The return arm drops the capture in both paths. -/
noncomputable def canonicalAssembly {X S D : τ}
    (entry : ofType (Φ := Φ) X ⟶ ofType (packedExitType [S, D]))
    (step : ofType (Φ := Φ) (Silmaril.product X S) ⟶
      ofType (Silmaril.product X D) ⨿ ofType (Silmaril.product X S)) :
    ofType (Φ := Φ) X ⟶ ofType D :=
  let drop := ofRegion (τ := τ) (productSndBranches (Φ := Φ) X D)
  dispatchArrow (entry ≫ exitSumArrow S D) drop (Paper.TypeCategory.iterate step ≫ drop)

/-- The two-label decoder as a guarded region over the exact sum. -/
def exitDecoder {τ : Type u} {Φ : Type v} : Region Φ :=
  let wk := Silmaril.DeBruijn.lift Nat.succ
  let left : Region Φ := .br 0 (.inl (.var 0))
  let right : Region Φ := .br 0 (.inr (.var 0))
  let tail := Region.case (.var 0) (left.renameVars wk) ((unpackExits ([] : LCtx τ)).renameVars wk)
  .case (.var 0) (right.renameVars wk) (tail.renameVars wk)

theorem exitDecoder_typed (S D : τ) :
    ValueBranches [packedExitType [S,D]] (exitDecoder (τ := τ) : Region Φ) [Silmaril.coprod D S] :=
  caseValueBranches (A := S) (B := Silmaril.coprod D Silmaril.empty)
    (.br rfl (.inr (.var rfl)))
    (caseValueBranches (A := D) (B := Silmaril.empty)
      (.br rfl (.inl (.var rfl))) (emptyExit_typed _))

/-- The normal form runs the carried-state loop in the repeat arm. -/
def canonicalRegion (X S : τ) (e b : Region Φ) : Region Φ :=
  let lift := Silmaril.DeBruijn.lift Nat.succ
  let drop : Region Φ := .let₂ (.var 0) (.br 0 (.var 0))
  Paper.RetainedCase.assembleCase
    (e.lsubst (fun _ => (exitDecoder (τ := τ)).renameVars lift))
    (Paper.PackedBody.applyPacked drop)
    (Paper.PackedBody.applyPacked ((SyntacticCategory.iterateRegion (Silmaril.product X S) b).lsubst
      (fun _ => drop.renameVars lift)))

theorem canonicalRegion_typed {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S,D]])
    (hb : ValueBranches [Silmaril.product X S] b
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]) :
    ValueBranches [X] (canonicalRegion X S e b) [D] :=
  let drop := productSndBranches (Φ := Φ) X D
  assembleCase_typed (seqValueBranches he (exitDecoder_typed S D)) (applyPacked_typed drop)
    (applyPacked_typed (seqValueBranches (iterateRegion_valueBranches hb) drop))

section ValueModel

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

/-- Remove the singleton label wrapper using its only injection. -/
noncomputable def labelPayloadIso (A : τ) : labelObj M [A] ≅ M.obj A where
  hom := singletonLabelPayload M A
  inv := labelInject M 0 rfl
  hom_inv_id := payload_labelInject M A
  inv_hom_id := labelInject_payload M A

/-- Pack the context and the local label payload as a syntactic product. -/
noncomputable def carriedIso (X A : τ) :
    ctxObj M [X] ⊗ labelObj M [A] ≅ M.obj (Silmaril.product X A) :=
  MonoidalCategory.whiskerLeftIso (ctxObj M [X]) (labelPayloadIso M A) ≪≫
    MonoidalCategory.whiskerRightIso (λ_ (M.obj X)) (M.obj A) ≪≫ (M.productIso X A).symm

/-- Decode the two labels into an exact sum with return on the left. -/
noncomputable def exitSum (S D : τ) :
    M.obj (packedExitType [S, D]) ⟶ M.obj (Silmaril.coprod D S) :=
  unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D] ≫
    coprod.map (singletonLabelPayload M D) (singletonLabelPayload M S) ≫
      (M.coprodIso D S).inv

variable {C : Type u₂} [Category.{v₂} C]

/-- Interpret a packed block at the context and local label interface of the dispatcher. -/
noncomputable def blockComputation (J : V ⥤ C) (X S D : τ)
    (f : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S,D]))) :
    J.obj (ctxObj M [X] ⊗ labelObj M [S]) ⟶ J.obj (labelObj M [D] ⨿ labelObj M [S]) :=
  J.map (carriedIso M X S).hom ≫ f ≫ J.map (unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D])

end ValueModel

section ComputationModel

universe u₁ v₁
variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp]
  [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  (J : V ⥤ Comp) [DistributiveFreydCategory J] (M : TypeModel τ V)
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)

/-- Interpret the carrier as a packed singleton object of the Paper category. -/
noncomputable def paperCarrier (X A : τ) :
    J.obj (ctxObj M [X] ⊗ labelObj M [A]) ≅ ofType (Φ := Φ) (Silmaril.product X A) :=
  J.mapIso (carriedIso M X A) ≪≫ objIso (Silmaril.product X A)

/-- The ordinary carried step of the actual block, in exact singleton coordinates. -/
noncomputable def carriedStep (X S D : τ)
    (b : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S,D]))) :
    ofType (Φ := Φ) (Silmaril.product X S) ⟶
      ofType (Silmaril.product X D) ⨿ ofType (Silmaril.product X S) :=
  reindexStep (paperCarrier J M objIso X S) (paperCarrier J M objIso X D)
    (contextualStep J (blockComputation M J X S D b))

end ComputationModel

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
