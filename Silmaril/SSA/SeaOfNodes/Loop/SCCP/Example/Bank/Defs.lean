module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Defs

/-! A Boolean and an eight-bit word share the same loop occurrences. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open Diamond.SCCP (Fact tupleFacts)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

abbrev fields : List (ValueSort Unit) := [.predicate, word]

inductive Op : Signature Unit where
  | advance : Op [.predicate, word] word
  | continues : Op [word] .predicate
  | isZero : Op [word] .predicate

def model : Model Op where
  value := fun _ => Byte
  run
    | .advance, .cons enabled (.cons old .nil) =>
      if enabled.down then BitVec.add old 1 else old
    | .continues, .cons next .nil => ⟨BitVec.ult next 3⟩
    | .isZero, .cons old .nil => ⟨BitVec.toNat old == 0⟩

instance bankEq : BankDecidableEq model.value (dataPorts fields) where
  atPort i := Fin.cases (motive := fun j => DecidableEq (Val model.value (dataPorts fields)[j]))
    (inferInstance : DecidableEq (ULift Bool))
    (fun j => Fin.cases (motive := fun k => DecidableEq (Val model.value (dataPorts fields)[k.succ]))
      (inferInstance : DecidableEq Byte) (fun k => k.elim0) j) i

abbrev HeaderSigs : List (List (Ty Unit)) := [[.value word], [.value .predicate], [.value .predicate]]

/-- The first feedback field forwards the old flag or reads the old word's
zero test. The second always uses the old flag and word. -/
def graph (cross : Bool) : Graph Op fields fields [] HeaderSigs word where
  preheader := .nil
  header :=
    .cons .advance (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
      (.cons .continues (.cons (.output ⟨0, by decide⟩ .head) .nil)
        (.cons .isZero (.cons (.arg (.tail (.tail (.tail .head)))) .nil) .nil))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
    | .backedge =>
      .cons (if cross then .output ⟨2, by decide⟩ .head else .arg (.tail (.tail .head)))
        (.cons (.output ⟨0, by decide⟩ .head) .nil)
  predicate := .output ⟨1, by decide⟩ .head
  result := .output ⟨0, by decide⟩ .head

def facts (enabled : Bool) (start : Byte) : Tuple (Fact model.value) (dataPorts fields) :=
  .cons (.constant ⟨enabled⟩) (.cons (.constant start) .nil)

def entry (enabled : Bool) (start : Byte) : Tuple (Val model.value) (dataPorts fields) :=
  .cons ⟨enabled⟩ (.cons start .nil)

def observe (bank : BankFacts model.value (dataPorts fields)) : Flat Bool × Flat Nat :=
  ((bank (0 : Fin 2)).map ULift.down, (bank (1 : Fin 2)).map BitVec.toNat)

/-- The backedge and exit marks, then the two latch facts and the exit fact. -/
def invariantReport : Bool × Bool × (Flat Bool × Flat Nat) × Flat Nat :=
  let state := solve model (graph false) (facts true 0)
  (decide (incomingIndex .backedge ∈ state.1), decide (exitIndex ∈ state.1),
    observe state.2.1, state.2.2.map BitVec.toNat)

/-- Isolate the Phi feedback equation by marking only the backedge. -/
def abstractCrossFeedback : Flat Bool × Flat Nat :=
  let old : State model.value fields word := ({incomingIndex .backedge}, tupleFacts (facts false 0), ⊥)
  observe (transfer model (graph true) (facts false 0) old).2.1

def nativeCrossFeedback : Option (Bool × Nat) :=
  match (graph true).step model (entry false 0) (entry false 0) with
  | .inl _ => none
  | .inr next => some ((next.get .head).down, BitVec.toNat (next.get (.tail .head)))

def runInvariant (budget : Nat) : Option Nat :=
  ((graph false).evalBackedges model budget (entry true 0)).map BitVec.toNat

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank
