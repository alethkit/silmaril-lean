module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Iteration.Thms

import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationITree

/-! # The selected joined iterator in the typed weak ITree model -/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Paper.Extension.Singleton (ofType ofRegion sumIso)
open Reification (canonicalIterate)
open SyntacticCategory (iterateRegion)

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]

local notation "Seed" => Step (τ := Ty κ) (Φ := Φ)
local notation "V" => AtomValues.carrier (κ := κ)
set_option hygiene false in
local notation "TypedCalls" => ⟨fun f x =>
  InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩

/-- The selected iterator evaluates to the guarded execution of the
one-label loop on any exact-sum representative of the normalized step. -/
theorem denoteITree_canonicalIterate_tree
    (raw : Primitive E Φ (Sigma V)) (compat : Compatible (κ' := κ) TypedCalls raw)
    {A B : Ty κ} {r : Region Φ} (hr : ValueBranches [A] r [Silmaril.coprod B A])
    (input : Ty.denote V A) (env : Env (Sigma V)) :
    (denoteITree raw compat
      (canonicalIterate (ofRegion (Seed) hr ≫ (sumIso (Seed) B A).hom)) input >>=
        fun b => pure (0, encodeValue V B b)) =
      region raw (extend env (encodeValue V A input)) (iterateRegion A r) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationITree.iterationTree raw compat hr input env

/-- For any joined step into the chosen coproduct, the inverse sum comparison
gives the exact return-or-repeat coordinates consumed by the ITree iterator. -/
theorem denoteITree_canonicalIterate
    (raw : Primitive E Φ (Sigma V)) (compat : Compatible (κ' := κ) TypedCalls raw)
    {A B : Ty κ} (f : ofType (Seed) A ⟶ ofType (Seed) B ⨿ ofType (Seed) A) (input : Ty.denote V A) :
    denoteITree raw compat (canonicalIterate f) input =
      Silmaril.Elgot.iter (denoteITree raw compat (f ≫ (sumIso (Seed) B A).inv)) input :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationITree.typedIterate raw compat f input

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta
