module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Defs

/-! # The visible pair-return fixture -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.ITree

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Paper.TypeCategory.ITree.Reflection
open Paper.Extension.Singleton (ofType ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Elgot.ITree

attribute [local instance] typeModel categoricalInstructions

local notation "Join" => JoinedStep (τ := Ty Atom) (Φ := Op) false
local notation "J" => typeJ (m := TreeModel)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
local notation "X" => payload
local notation "Y" => (product Output Output)

abbrev Operand := Ty.denote Atoms payload
abbrev Result := OutputValue × OutputValue

theorem call_typed (p : Op) : Tm.HasType [X] (.op p (.var 0)) Output := .op (.var rfl)

/-- Return a pair of distinguishable visible calls. -/
def pairArrow : ofType Join X ⟶ ofType Join Y :=
  ofRegion Join (returnRegion_typed (.pair (call_typed .poll) (call_typed .query)))

/-- The two calls as successive guarded binders. -/
def sequencedArrow : ofType Join X ⟶ ofType Join Y :=
  ofRegion Join (pairSequence_typed (call_typed .poll) (call_typed .query))

noncomputable def interpretation : Paper.Extension.Singleton.TypeCategory Join ⥤ Kleisli (ofTypeMonad TreeModel) :=
  letI := regionTypingCoherent raw compatible
  Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)

/-- Both requests use the original operand and retain their own replies. -/
def expected (x : Operand) : TreeModel Result :=
  vis (.request .poll x.down) (fun a => vis (.request .query x.down) (fun b => pure (reply a, reply b)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.ITree
