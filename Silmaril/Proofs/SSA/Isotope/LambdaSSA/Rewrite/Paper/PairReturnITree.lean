module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.ITree.Defs

/-! # Observable ordering for two returned calls -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithPairReturns
open Paper.WithPairReturns.ITree

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
local notation "inlJoin" => (fun h => Or.inl (Or.inr (Or.inl h)))

theorem pairArrow_generated : Generated Join pairArrow :=
  generated_returnPair Join Or.inr inlJoin (call_typed .poll) (call_typed .query)
    (.primitive Op.poll) (.primitive Op.query)

theorem pairArrow_eq_sequenced : pairArrow = sequencedArrow :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Join _ _).2 <|
    .extra (returnRegion_typed (.pair (call_typed .poll) (call_typed .query))).hasType
      (pairSequence_typed (call_typed .poll) (call_typed .query)).hasType
      (Or.inr (.seq (call_typed .poll) (call_typed .query)))

private def decodeTag : Value (Sigma Atoms) → Option OutputValue
  | .inl (.atom atom) => some (.inl atom.2)
  | .inr (.atom atom) => some (.inr atom.2)
  | _ => none

private def decode : Transfer (Sigma Atoms) → TreeModel Result
  | (0, .pair a b) =>
    match decodeTag a, decodeTag b with
    | some a, some b => pure (a, b)
    | _, _ => diverge
  | _ => diverge

private def encode (x : Result) : Transfer (Sigma Atoms) :=
  (0, encodeValue Atoms Y x)

private theorem decode_encode (x : Result) : decode (encode x) = pure x := by
  obtain ⟨a,b⟩ := x
  cases a <;> cases b <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem pairArrow_visible (x : Operand) :
    (Paper.WithPairReturns.ITree.interpretation.map pairArrow).of x = expected x := by
  let := regionTypingCoherent raw compatible
  let ht := pairSequence_typed (call_typed .poll) (call_typed .query)
  rw [pairArrow_eq_sequenced]
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)).map (ofRegion Join ht)).of x = expected x
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  have eval := singletonDenote_tree raw compatible ht.hasType x (fun _ => .unit)
  have rawBody :
      region raw (extend (fun _ => .unit) (encodeValue Atoms X x))
        (Paper.UnaryReturn.Beta.Constructors.pairSequence (.op .poll (.var 0)) (.op .query (.var 0))) =
      (expected x >>= fun y => pure (encode y)) := by
    simp [Paper.UnaryReturn.Beta.Constructors.pairSequence, region, term, raw, encodeValue,
      encode, expected, extend, vis_bind, -bind_pure_comp, Tm.rename]
  let result : TreeModel Result := (Semantics.Categorical.denoteSingletonRegion J M ht.hasType).of x
  change (result >>= fun y => pure (encode y)) =
    region raw (extend (fun _ => .unit) (encodeValue Atoms X x)) _ at eval
  change result = expected x
  have eq := eval.trans rawBody
  simpa only [bind_assoc, pure_bind, decode_encode, bind_pure] using congrArg (· >>= decode) eq

theorem query_is_not_first (x : Operand) (k : Sum Nat Nat → TreeModel Result) :
    (Paper.WithPairReturns.ITree.interpretation.map pairArrow).of x ≠ vis (.request .query x.down) k := by
  rw [pairArrow_visible]
  intro h
  have seen := congrArg out h
  simp only [expected, out_vis, Part.some_inj, Visible.vis.injEq, heq_eq_eq, true_and,
    and_true, Call.request.injEq] at seen
  cases seen.1

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnITree
