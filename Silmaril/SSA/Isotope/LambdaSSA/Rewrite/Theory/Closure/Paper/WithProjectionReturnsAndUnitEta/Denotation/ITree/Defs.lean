module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms

/-! # Typed weak interaction trees for the joined singleton category -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.Extension.Singleton (ofType)

universe v q

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]

set_option hygiene false in
local notation "Seed" => Step (τ := Ty κ) (Φ := Φ)
set_option hygiene false in
local notation "V" => AtomValues.carrier (κ := κ)
set_option hygiene false in
local notation "J" => typeJ (m := ModelTree E)
set_option hygiene false in
local notation "T" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)
set_option hygiene false in
local notation "TypedCalls" => ⟨fun f x =>
  InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩

/-- Evaluate an actual joined singleton arrow using the same typed and
erased primitive profiles as the guarded representative interpretation. -/
noncomputable def denoteITree
    (raw : Primitive E Φ (Sigma V)) (compat : Compatible (κ' := κ) TypedCalls raw)
    {A B : Ty κ} (f : ofType (Seed) A ⟶ ofType (Seed) B) (input : Ty.denote V A) :
    ModelTree E (Ty.denote V B) :=
  let := regionTypingCoherent raw compat
  (denoteArrow (J) (T) (fun _ _ => ⟨rfl, rfl⟩) f).of input

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
