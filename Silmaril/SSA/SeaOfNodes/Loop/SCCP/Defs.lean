module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-! Executable occurrence and constant equations for a typed carried bank. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers evalFacts readLocal tupleFacts)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

/-- One data value is latched at the existing native Loop Region. -/
abbrev Program (Op : Signature.{u, v} Data) (inputs : List (ValueSort Data)) (carry : Data)
    (entrySigs headerSigs : List (List (Ty Data))) (out : ValueSort Data) :=
  Graph Op inputs [.data carry] entrySigs headerSigs out

abbrev Executable := Finset (Fin 3)

def incomingIndex : Incoming → Fin 3
  | .entry => 0
  | .backedge => 1

def exitIndex : Fin 3 := 2

/-- One flat fact at each typed port, ordered pointwise. -/
abbrev BankFacts (value : Data → Type w) (ports : List (Ty Data)) :=
  (i : Fin ports.length) → Fact value ports[i]

/-- The pointwise joins only need decidable equality at the carried ports. -/
class BankDecidableEq (value : Data → Type w) (ports : List (Ty Data)) where
  atPort (i : Fin ports.length) : DecidableEq (Val value ports[i])

/-- Read a numbered abstract bank as the native ordered tuple. -/
def bankTuple {value : Data → Type w} :
    {ports : List (Ty Data)} → BankFacts value ports → Tuple (Fact value) ports
  | [], _ => .nil
  | _ :: _, bank => .cons (bank 0) (bankTuple fun i => bank i.succ)

def BankCovers {value : Data → Type w} {ports : List (Ty Data)}
    (bank : BankFacts value ports) (concrete : Tuple (Val value) ports) : Prop :=
  TupleCovers (bankTuple bank) concrete

abbrev State (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) :=
  Executable × (BankFacts value (dataPorts carried) × Flat (sortValue value out))

structure HeaderFacts (value : Data → Type w) (carried : List (ValueSort Data)) (out : ValueSort Data) where
  guard : Flat (ULift.{w} Bool)
  feedback : BankFacts value (dataPorts carried)
  result : Flat (sortValue value out)

variable (m : Model.{u, v, w} Op) (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

/-- Read the entire entry column in the preheader context. -/
def entryFacts : BankFacts m.value (dataPorts carried) :=
  let locals := evalFacts m input g.preheader PUnit.unit
  tupleFacts ((g.phiInputs .entry).read input locals)

/-- Read every feedback operand, the guard, and the result in the same
producer environment built from the old latch. -/
def headerFacts (latch : BankFacts m.value (dataPorts carried)) : HeaderFacts m.value carried out :=
  let args := appendTuple (bankTuple latch) input
  let locals := evalFacts m args g.header PUnit.unit
  ⟨readLocal args locals g.predicate,
    tupleFacts ((g.phiInputs .backedge).read args locals),
    readLocal args locals g.result⟩

def successors : Flat (ULift.{w} Bool) → Executable
  | .bottom => ∅
  | .constant test => if test.down then {incomingIndex .backedge} else {exitIndex}
  | .overdefined => {incomingIndex .backedge, exitIndex}

/-- Start enables the entry occurrence. An enabled header may then mark
the tail successors permitted by its abstract guard. -/
def control (old : Executable) (guard : Flat (ULift.{w} Bool)) : Executable :=
  insert (incomingIndex .entry)
    (if incomingIndex .entry ∈ old then successors guard else ∅)

def gate {α : Type*} (old : Executable) (i : Fin 3) (fact : Flat α) : Flat α :=
  if i ∈ old then fact else ⊥

/-- Join the entry and feedback columns exactly over marked occurrences. -/
def phiFact {α : Type*} [DecidableEq α] (old : Executable) (entry feedback : Flat α) : Flat α :=
  Flat.join (gate old (incomingIndex .entry) entry) (gate old (incomingIndex .backedge) feedback)

/-- Apply the same occurrence marks to every typed Phi in the bank. -/
def phiFacts {value : Data → Type w} {ports : List (Ty Data)}
    [equal : BankDecidableEq value ports]
    (edges : Executable) (entry feedback : BankFacts value ports) : BankFacts value ports :=
  fun i => @phiFact _ (equal.atPort i) edges (entry i) (feedback i)

/-- Every right-hand side reads the old assignment. The complete feedback
column is read before the pointwise joins build the next bank. -/
def transfer [BankDecidableEq m.value (dataPorts carried)]
    (old : State m.value carried out) : State m.value carried out :=
  let header := headerFacts m g input old.2.1
  (control old.1 header.guard,
    phiFacts old.1 (entryFacts m g input) header.feedback,
    gate old.1 exitIndex header.result)

/-- Finite native prefixes, including prefixes with no eventual return.
The index records the occurrence by which the header was reached. -/
inductive Arrives (entry : Tuple (Val m.value) (dataPorts inputs)) :
    Incoming → Nat → Tuple (Val m.value) (dataPorts carried) → Prop where
  | entry : Arrives entry .entry 0 (g.initial m entry)
  | backedge {via count old next} (arrived : Arrives entry via count old)
      (taken : g.step m entry old = .inr next) :
      Arrives entry .backedge (count + 1) next

end Silmaril.SSA.SeaOfNodes.Loop.SCCP
