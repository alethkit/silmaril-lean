module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.ITree.Defs

/-! # The producer reply is passed to the consumer exactly once -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallITree

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedCallReturns
open Paper.WithComputedCallReturns.Example
open Paper.WithComputedCallReturns.Example.ITree
open CategoryTheory
open Paper.Extension.Singleton (ofRegion)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Elgot.ITree

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := TreeModel)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

private def encode (x : PayloadValue) : Transfer (Sigma Atoms) :=
  (0, encodeValue Atoms Payload x)

private def decode : Transfer (Sigma Atoms) → TreeModel PayloadValue
  | (0, .atom a) => pure a.2
  | _ => diverge

private theorem decode_encode (x : PayloadValue) : decode (encode x) = pure x := rfl

set_option backward.isDefEq.respectTransparency false in
theorem sequenced_visible (x : PayloadValue) :
    (interpretation.map sequencedArrow).of x = expected x := by
  let := regionTypingCoherent raw compatible
  let ht := returnRegion_typed sequenced_typed
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (joined_seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩))).map (ofRegion Seed ht)).of x = expected x
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  have eval := singletonDenote_tree raw compatible ht.hasType x (fun _ => .unit)
  have rawBody :
      region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x)) (returnRegion sequenced) =
        (expected x >>= fun y => pure (encode y)) := by
    change region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x))
      (.let₁ (.op .produce (.var 0)) (.let₁ (.var 0) (.let₁ (.op .consume (.var 0)) (.br 0 (.var 0))))) = _
    simp [region, term, raw, reply, encodeValue, encode, expected, extend, vis_bind, -bind_pure_comp]
  let result : TreeModel PayloadValue := (Semantics.Categorical.denoteSingletonRegion J M ht.hasType).of x
  change (result >>= fun y => pure (encode y)) =
    region raw (extend (fun _ => .unit) (encodeValue Atoms Payload x)) _ at eval
  change result = expected x
  simpa only [bind_assoc, pure_bind, decode_encode, bind_pure] using congrArg (· >>= decode) (eval.trans rawBody)

theorem nested_visible (x : PayloadValue) :
    (interpretation.map nestedArrow).of x = expected x := by
  have eq : nestedArrow = sequencedArrow := nested_eq_sequenced false
  rw [eq]
  exact sequenced_visible x

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedCallITree
