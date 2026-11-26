module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-! Executable occurrence and constant equations for a single carried loop value. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact evalFacts readLocal)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carry : Data}
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

abbrev State (value : Data → Type w) (carry : Data) (out : ValueSort Data) :=
  Executable × (Flat (value carry) × Flat (sortValue value out))

structure HeaderFacts (value : Data → Type w) (carry : Data) (out : ValueSort Data) where
  guard : Flat (ULift.{w} Bool)
  feedback : Flat (value carry)
  result : Flat (sortValue value out)

variable (m : Model.{u, v, w} Op) (g : Program Op inputs carry entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

/-- Read the entry column in the preheader context. -/
def entryFact : Flat (m.value carry) :=
  let locals := evalFacts m input g.preheader PUnit.unit
  readLocal input locals ((g.phiInputs .entry).get .head)

/-- Abstractly run one producer table in dependency order on the old latch.
The feedback and exit wires share that table with the guard wire. -/
def headerFacts (latch : Flat (m.value carry)) : HeaderFacts m.value carry out :=
  let args : Tuple (Fact m.value) (headerPorts inputs [.data carry]) :=
    appendTuple (.cons (F := Fact m.value) (t := RVSDG.PortType.value (.data carry)) latch .nil) input
  let locals := evalFacts m args g.header PUnit.unit
  ⟨readLocal args locals g.predicate,
    readLocal args locals ((g.phiInputs .backedge).get .head),
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

/-- Every right-hand side reads the old assignment. In particular the Phi
depends on the old latch through the backedge column and its guard. -/
def transfer [DecidableEq (m.value carry)] (old : State m.value carry out) : State m.value carry out :=
  let header := headerFacts m g input old.2.1
  (control old.1 header.guard,
    phiFact old.1 (entryFact m g input) header.feedback,
    gate old.1 exitIndex header.result)

/-- Finite native prefixes, including prefixes with no eventual return.
The index records the occurrence by which the header was reached. -/
inductive Arrives (entry : Tuple (Val m.value) (dataPorts inputs)) :
    Incoming → Nat → Tuple (Val m.value) (dataPorts [.data carry]) → Prop where
  | entry : Arrives entry .entry 0 (g.initial m entry)
  | backedge {via count old next} (arrived : Arrives entry via count old)
      (taken : g.step m entry old = .inr next) :
      Arrives entry .backedge (count + 1) next

end Silmaril.SSA.SeaOfNodes.Loop.SCCP
