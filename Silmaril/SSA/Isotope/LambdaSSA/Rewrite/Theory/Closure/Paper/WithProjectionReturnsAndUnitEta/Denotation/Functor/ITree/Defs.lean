module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Functor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Defs

/-! # The joined singleton functor into typed weak interaction trees -/

@[expose] public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.Extension.Singleton (ofType)

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]
  (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

set_option hygiene false in
local notation "TypedCalls" => ⟨fun f x =>
  InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩

variable (compat : Compatible (κ' := κ) TypedCalls raw)

local notation "K" => typeJ (m := ModelTree E)
local notation "M" => Silmaril.Isotope.LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)
local notation "Obj" => ofType (Step (τ := Ty κ) (Φ := Φ))

/-- The guarded weak ITree functor descends through the sound joined quotient. -/
noncomputable def weakITreeFunctor :
    TypeCategory (τ := Ty κ) (Φ := Φ) ⥤ Kleisli (ofTypeMonad (ModelTree E)) :=
  let := regionTypingCoherent raw compat
  denoteFunctor (K) (M) (fun _ _ => ⟨rfl, rfl⟩)

/-- The comparison from the image of the joined chosen sum to the Kleisli chosen sum. -/
noncomputable def weakITreeFunctorCoprodIso (A B : Ty κ) :
    (weakITreeFunctor raw compat).obj (Obj A ⨿ Obj B) ≅
      (weakITreeFunctor raw compat).obj (Obj A) ⨿ (weakITreeFunctor raw compat).obj (Obj B) :=
  let := regionTypingCoherent raw compat
  denoteFunctorCoprodIso (Φ := Φ) (K) (M) (fun _ _ => ⟨rfl, rfl⟩) A B

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
