module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Denotation.UniversalProperty.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.ITree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Denotation.UniversalProperty.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.ITree.Thms

/-! # Generated comparison for visible pair and computed-call returns -/

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedGeneratedDenotationExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open Paper.Extension.Singleton.Generation
open Semantics.Interaction.Typed (typeModel categoricalInstructions regionTypingCoherent)
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

namespace Pair

open Paper.TypeCategory.ITree.Reflection (Atom Op TreeModel Output payload raw compatible)
open Paper.WithPairReturns.ITree (Operand pairArrow pairArrow_generated pairArrow_visible expected)

attribute [local instance] typeModel categoricalInstructions

local notation "Jm" => typeJ (m := TreeModel)
local notation "Mm" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
local notation "tensorShared" => (fun _ _ => Exists.intro rfl rfl)
local notation "Seed" => Paper.WithPairReturns.JoinedStep (τ := Ty Atom) (Φ := Op) false
local notation "ModelInterpretation" => Domain.Interpretation Seed (Coordinates.ofModel Jm Mm)
  (InstructionModel.denote (J := Jm) (M := Mm))

local instance : Semantics.Categorical.RegionTypingCoherent (Φ := Op) Jm Mm :=
  regionTypingCoherent raw compatible

private def pair : Domain.ofType Seed payload ⟶ Domain.ofType Seed (product Output Output) :=
  Domain.ofGenerated Seed pairArrow_generated

-- The candidate lives only on the generated category. Both primitive requests use the original input.
example (G : ModelInterpretation) (x : Operand) :
    (Domain.mapInCoordinates Seed G.functor G.objIso pair).of x = expected x := by
  rw [← Paper.WithPairReturns.generatedInterpretation_map_eq false Jm Mm tensorShared G pair]
  exact pairArrow_visible x

end Pair

namespace ComputedCall

open Paper.WithComputedCallReturns.Example (Atom Op Payload nested_generated)
open Paper.WithComputedCallReturns.Example.ITree
  (TreeModel PayloadValue Seed nestedArrow nested_visible expected raw compatible)

attribute [local instance] typeModel categoricalInstructions

local notation "Jm" => typeJ (m := TreeModel)
local notation "Mm" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
local notation "tensorShared" => (fun _ _ => Exists.intro rfl rfl)
local notation "ModelInterpretation" => Domain.Interpretation Seed (Coordinates.ofModel Jm Mm)
  (InstructionModel.denote (J := Jm) (M := Mm))

local instance : Semantics.Categorical.RegionTypingCoherent (Φ := Op) Jm Mm :=
  regionTypingCoherent raw compatible

private def nested : Domain.ofType Seed Payload ⟶ Domain.ofType Seed Payload :=
  Domain.ofGenerated Seed (nested_generated false)

-- The consumer takes the producer's reply even though the written operand is a unary let.
example (G : ModelInterpretation) (x : PayloadValue) :
    (Domain.mapInCoordinates Seed G.functor G.objIso nested).of x = expected x := by
  rw [← Paper.WithComputedCallReturns.generatedInterpretation_map_eq false Jm Mm tensorShared G nested]
  exact nested_visible x

end ComputedCall

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedGeneratedDenotationExample
