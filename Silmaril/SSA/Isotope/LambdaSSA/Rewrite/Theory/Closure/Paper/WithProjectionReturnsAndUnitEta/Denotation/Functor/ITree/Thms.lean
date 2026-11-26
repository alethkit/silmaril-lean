module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Functor.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Thms

/-! # Factorization, finite coproducts and iteration in the joined ITree functor -/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.Extension.Singleton (ofType)
open Reification (canonicalIterate)

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
local notation "F" => weakITreeFunctor raw compat

/-- The ordinary guarded ITree functor factors through projection to the join. -/
theorem projection_comp_weakITreeFunctor :
    (projection (τ := Ty κ) (Φ := Φ)) ⋙ (F) = Paper.TypeCategory.weakITreeFunctor raw compat :=
  let := regionTypingCoherent raw compat
  projection_comp_denoteFunctor (K) (M) (fun _ _ => ⟨rfl, rfl⟩)

/-- The bundled arrow computes the existing joined weak ITree evaluation. -/
theorem weakITreeFunctor_map_apply {A B : Ty κ} (f : Obj A ⟶ Obj B)
    (a : Ty.denote AtomValues.carrier A) :
    ((F).map f).of a = denoteITree raw compat f a :=
  rfl

/-- The descended functor preserves the empty coproduct and all finite coproducts. -/
theorem weakITreeFunctor_preservesFiniteCoproducts : PreservesFiniteCoproducts (F) :=
  let := regionTypingCoherent raw compat
  denoteFunctor_preservesFiniteCoproducts (Φ := Φ) (K) (M) (fun _ _ => ⟨rfl, rfl⟩)

/-- The comparison sends the chosen Kleisli injections to the mapped joined injections. -/
theorem weakITreeFunctor_coprodComparison (A B : Ty κ) :
    coprodComparison (F) (Obj A) (Obj B) = (weakITreeFunctorCoprodIso raw compat A B).inv :=
  rfl

/-- The functor commutes with joined iteration using its canonical coproduct comparison. -/
theorem weakITreeFunctor_map_canonicalIterate {A B : Ty κ} (f : Obj A ⟶ Obj B ⨿ Obj A) :
    (F).map (canonicalIterate f) =
      CategoryTheory.iterate ((F).map f ≫ (weakITreeFunctorCoprodIso raw compat B A).hom) :=
  let := regionTypingCoherent raw compat
  denoteFunctor_map_canonicalIterate (K) (M) (fun _ _ => ⟨rfl, rfl⟩) f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
