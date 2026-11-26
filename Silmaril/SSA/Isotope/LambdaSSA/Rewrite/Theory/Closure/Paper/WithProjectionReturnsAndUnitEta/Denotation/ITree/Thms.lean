module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Thms

/-! # Representative equations for the interpreted joined arrow -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.Extension.Singleton (ofRegion)

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

/-- The descended arrow evaluates to the typed denotation of any of its
guarded representatives. -/
theorem denoteITree_ofRegion
    (raw : Primitive E Φ (Sigma V)) (compat : Compatible (κ' := κ) TypedCalls raw)
    {A B : Ty κ} {r : Region Φ} (hr : ValueBranches [A] r [B]) (input : Ty.denote V A) :
    denoteITree raw compat (ofRegion (Seed) hr) input =
      (Semantics.Categorical.denoteSingletonRegion (J) (T) hr.hasType).of input := by
  unfold denoteITree
  dsimp only
  rw [denoteArrow_ofRegion]

/-- Encoding the typed output gives the same weak ITree as running the
literal representative on the encoded input. -/
theorem denoteITree_tree
    (raw : Primitive E Φ (Sigma V)) (compat : Compatible (κ' := κ) TypedCalls raw)
    {A B : Ty κ} {r : Region Φ} (hr : ValueBranches [A] r [B])
    (input : Ty.denote V A) (env : Env (Sigma V)) :
    (denoteITree raw compat (ofRegion (Seed) hr) input >>= fun b => pure (0, encodeValue V B b)) =
      region raw (extend env (encodeValue V A input)) r := by
  rw [denoteITree_ofRegion]
  exact singletonDenote_tree raw compat hr.hasType input env

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
