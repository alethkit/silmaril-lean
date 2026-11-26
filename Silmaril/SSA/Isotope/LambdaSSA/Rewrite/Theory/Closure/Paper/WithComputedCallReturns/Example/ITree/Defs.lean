module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Thms

/-! # The free ITree interpretation of the two-call example -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example.ITree

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree

instance : AtomValues Atom where
  carrier _ := ULift.{1} Nat

abbrev Atoms := AtomValues.carrier (κ := Atom)

inductive Request : Type → Type where
  | call (p : Op) (operand : Nat) : Request Nat

abbrev TreeModel := ModelTree Request
abbrev PayloadValue := Ty.denote Atoms Payload

def reply (n : Nat) : PayloadValue := ⟨n⟩

attribute [local instance] typeModel

instance : InstructionModel Op (Ty Atom) Bool TreeModel where
  denote p x := vis (.call p x.down) (fun answer => pure (reply answer))
  denotePure p h := by cases h
  denote_pure p h := by cases h

def raw : Primitive Request Op (Sigma Atoms) := fun p arg =>
  match arg with
  | .atom a => vis (.call p a.2.down) (fun answer => pure (encodeValue Atoms Payload (reply answer)))
  | _ => diverge

theorem compatible :
    Compatible (κ' := Atom) ⟨fun p x =>
      InstructionModel.denote (τ := Ty Atom) (ε := Bool) (m := TreeModel) p x⟩ raw := by
  intro p x
  change vis (.call p x.down) (fun answer => pure (encodeValue Atoms Payload (reply answer))) =
    ((vis (.call p x.down) (fun answer => (pure (reply answer) : TreeModel PayloadValue))) >>= fun y =>
      pure (encodeValue Atoms Payload y))
  simp only [vis_bind, pure_bind]

attribute [local instance] categoricalInstructions

abbrev Seed := JoinedStep (τ := Ty Atom) (Φ := Op) false

/-- Evaluate the actual interpreted quotient arrows in the free ITree model. -/
noncomputable def interpretation :
    Paper.Extension.Singleton.TypeCategory Seed ⥤ Kleisli (ofTypeMonad TreeModel) :=
  letI := regionTypingCoherent raw compatible
  Paper.Extension.Singleton.denoteFunctor (typeJ (m := TreeModel))
    (Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)) (fun _ _ => ⟨rfl, rfl⟩)
    (joined_seedDenotes false _ _ (fun _ _ => ⟨rfl, rfl⟩))

def nestedArrow : ofType Seed Payload ⟶ ofType Seed Payload :=
  ofRegion Seed (returnRegion_typed nested_typed)

def sequencedArrow : ofType Seed Payload ⟶ ofType Seed Payload :=
  ofRegion Seed (returnRegion_typed sequenced_typed)

/-- The producer is called at the original input. Its reply is the sole
argument of the consumer, whose reply is returned immediately. -/
def expected (x : PayloadValue) : TreeModel PayloadValue :=
  vis (.call .produce x.down) (fun produced =>
    vis (.call .consume produced) (fun consumed => pure ⟨consumed⟩))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example.ITree
