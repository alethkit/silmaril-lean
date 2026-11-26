module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Thms

/-! # A free typed ITree profile and two acyclic guarded arrows -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection

open CategoryTheory
open Silmaril.Isotope.Semantics (encodeValue)
open Semantics.Interaction.Typed
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)

inductive Atom : Type 1 where
  | nat

instance : AtomValues Atom where
  carrier _ := ULift.{1} Nat

abbrev payload : Ty Atom := .base .nat
abbrev Output : Ty Atom := .coprod payload payload
abbrev Input : Ty Atom := .coprod Output payload

inductive Op where
  | poll
  | query

instance : HasTy Op (Ty Atom) where
  src _ := payload
  trg _ := Output

instance : HasEff Op Bool where
  eff _ := true

/-- Every call exposes its opcode and full operand and accepts a tag and an
arbitrary natural number in reply. -/
inductive Call : Type → Type where
  | request (op : Op) (operand : Nat) : Call (Sum Nat Nat)

abbrev TreeModel := ModelTree Call
abbrev Atoms := AtomValues.carrier (κ := Atom)
abbrev InputValue := Ty.denote Atoms Input
abbrev OutputValue := Ty.denote Atoms Output

/-- Embed the small response type into the typed value universe. -/
def reply (b : Sum Nat Nat) : OutputValue :=
  Sum.map ULift.up ULift.up b

attribute [local instance] typeModel

instance : InstructionModel Op (Ty Atom) Bool TreeModel where
  denote op x := vis (.request op x.down) (fun b => pure (reply b))
  denotePure op h := by cases h
  denote_pure op h := by cases h

def raw : Semantics.Interaction.Primitive Call Op (Sigma Atoms) := fun op arg =>
  match arg with
  | .atom a => vis (.request op a.2.down) (fun b => pure (encodeValue Atoms Output (reply b)))
  | _ => diverge

theorem compatible :
    Compatible (κ' := Atom) ⟨fun op x =>
      InstructionModel.denote (τ := Ty Atom) (ε := Bool) (m := TreeModel) op x⟩ raw := by
  intro op x
  change vis (.request op x.down) (fun b => pure (encodeValue Atoms Output (reply b))) =
    ((vis (.request op x.down) (fun b => (pure (reply b) : TreeModel _))) >>= fun y =>
      pure (encodeValue Atoms Output y))
  simp only [vis_bind, pure_bind]

/-- The right outer branch invokes the primitive and forwards its typed reply. -/
def pollRegion : Region Op :=
  .let₁ (.op .poll (.var 0)) (.br 0 (.var 0))

/-- On the left, a term-level case swaps the tag before the guarded return. -/
def termCase : Region Op :=
  .case (.var 0)
    (.let₁ (.case (.var 0) (.inr (.var 0)) (.inl (.var 0))) (.br 0 (.var 0)))
    pollRegion

/-- On the left, a region-level case selects between two guarded returns. -/
def regionCase : Region Op :=
  .case (.var 0)
    (.case (.var 0) (.br 0 (.inr (.var 0))) (.br 0 (.inl (.var 0))))
    pollRegion

theorem termCase_typed : ValueBranches [Input] termCase [Output] :=
  .case (.var rfl) (.let₁ (.case (.var rfl) (.inr (.var rfl)) (.inl (.var rfl))) (.br rfl (.var rfl)))
    (.let₁ (.op (.var rfl)) (.br rfl (.var rfl)))

theorem regionCase_typed : ValueBranches [Input] regionCase [Output] :=
  .case (.var rfl) (.case (.var rfl) (.br rfl (.inr (.var rfl))) (.br rfl (.inl (.var rfl))))
    (.let₁ (.op (.var rfl)) (.br rfl (.var rfl)))

def termArrow : ofType (Φ := Op) Input ⟶ ofType Output :=
  ofRegion termCase_typed

def regionArrow : ofType (Φ := Op) Input ⟶ ofType Output :=
  ofRegion regionCase_typed

noncomputable def interpretation : TypeCategory (τ := Ty Atom) Op ⥤ Kleisli (ofTypeMonad TreeModel) :=
  weakITreeFunctor raw compatible

/-- Apply the actual quotient interpretation to an input value. -/
noncomputable def run (f : ofType (Φ := Op) Input ⟶ ofType Output) (a : InputValue) :
    TreeModel OutputValue :=
  (interpretation.map f).of a

/-- The shared tree swaps the original sum tag or makes a visible call.
The two reply tags and their numeric payloads are supplied by the handler. -/
def behavior : InputValue → TreeModel OutputValue
  | .inl b => pure b.swap
  | .inr arg => vis (.request .poll arg.down) (fun b => pure (reply b))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection
