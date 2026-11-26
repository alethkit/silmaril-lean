module

public import Mathlib.Data.Set.Insert
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # A guarded iteration fixture over one opaque atomic sort -/

@[expose] public section

open CategoryTheory
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.ModelAudit.InvariantCarrier

inductive AtomSort : Type 1 where | key
abbrev Atom := ULift.{1} (Set Nat)
abbrev carrier (_ : AtomSort) : Type 1 := Atom
abbrev state : Ty AtomSort := .base .key
abbrev result : Ty AtomSort := .coprod .unit state
abbrev IsSingleton (x : Atom) : Prop := ∃ n : Nat, x.down = {n}

abbrev Invariant := {x : Atom // IsSingleton x}

/-- A singleton-set payload repeats unchanged. Every other payload returns unit. -/
noncomputable def next (x : Atom) : PUnit.{2} ⊕ Atom := by
  classical
  exact if IsSingleton x then .inr x else .inl PUnit.unit

/-- The finite return traces of the deterministic step. -/
inductive Returns : Atom → Prop where
  | done {x : Atom} (out : next x = .inl PUnit.unit) : Returns x
  | recur {x y : Atom} (out : next x = .inr y) (thenReturns : Returns y) : Returns x

inductive Op where | test
instance : HasTy Op (Ty AtomSort) := ⟨fun _ => state, fun _ => result⟩
instance : HasEff Op Bool := ⟨fun _ => true⟩

/-- Evaluate the chosen primitive once, then return its tagged result. -/
def body : Region Op := .let₁ (.op .test (.var 0)) (.br 0 (.var 0))

theorem body_typed : ValueBranches [state] body [result] :=
  .let₁ (.op (.var rfl)) (.br rfl (.var rfl))

instance : AtomValues AtomSort := ⟨carrier⟩
attribute [local instance] typeModel categoricalInstructions
abbrev Events : Type → Type := fun _ => Empty
abbrev TreeM := ModelTree Events
abbrev computation := typeJ (m := TreeM)
noncomputable abbrev typeInterpretation := ofMonadicTypeModel (τ := Ty AtomSort)

noncomputable instance : InstructionModel Op (Ty AtomSort) Bool TreeM where
  denote _ x := pure (next x)
  denotePure _ _ x := next x
  denote_pure _ _ _ := rfl

noncomputable def raw : Primitive Events Op (Sigma carrier) :=
  fun _ x => match x with
    | .atom ⟨_, atom⟩ => pure (encodeValue carrier result (next atom))
    | _ => diverge

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.ModelAudit.InvariantCarrier
