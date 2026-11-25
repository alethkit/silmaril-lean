module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Packed arrows for the entry and body of a one-block CFG -/

@[expose] public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X S D : τ} {e b : Region Φ}

/-- Retag the two exits using the linked packed-exit encoding. -/
def packLocalExits (r : Region Φ) (L : LCtx τ) : Region Φ :=
  r.linkExits L (fun i => .br 0 (packedExitArg i (.var 0)))

/-- The one-label entry on its original singleton input. -/
theorem entry_typed (h : HasType [X] e [S, D]) :
    HasType [X] (packLocalExits e [S, D]) [packedExitType [S, D]] :=
  h.linkExits (fun _ _ hi => ((packExits_valueFamily [X] [S, D]) hi).hasType)

/-- The local block on a record of the capture and its feedback payload. -/
theorem block_typed (h : HasType [S, X] b [S, D]) :
    HasType [packedInputType [S, X]] (packLocalExits b.packInputs [S, D]) [packedExitType [S, D]] :=
  h.packInputs.linkExits
    (fun _ _ hi => ((packExits_valueFamily [packedInputType [S, X]] [S, D]) hi).hasType)

/-- Decode a packed exit through the linked dispatcher. -/
def decodeExits (r : Region Φ) (L : LCtx τ) : Region Φ :=
  r.linkExits [packedExitType L] (fun _ => unpackExits L)

open PackedBody (applyPacked)

/-- Assemble a single outer feedback block from packed producers. The block
receives the captured input paired with the local feedback payload. -/
def guardedCfg (S D : τ) (e b : Region Φ) : Region Φ :=
  .cfg (decodeExits e [S, D]) 1 (fun _ => decodeExits (applyPacked b) [S, D])

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (M : TypeModel τ V)

/-- Run the packed entry, with its result selecting immediate return or
feedback. On feedback run the packed block, keeping the original capture. -/
noncomputable def assemble (X S D Record : τ)
    (input : ctxObj M [S, X] ⟶ M.obj Record)
    (entry : J.obj (M.obj X) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (block : J.obj (M.obj Record) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    J.obj (M.obj X) ⟶ J.obj (M.obj D) :=
  let E := ctxObj M [X]
  let split := J.map (unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D])
  J.map ((λ_ (M.obj X)).inv) ≫
    caseWithContext J (J.map ((λ_ (M.obj X)).hom) ≫ entry ≫ split)
      (J.map (snd E (labelObj M [D])))
      (contextualLoop J (J.map ((E ◁ singletonLabelPayload M S) ≫ input) ≫ block ≫ split)) ≫
    J.map (singletonLabelPayload M D)

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
