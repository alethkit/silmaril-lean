module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms

/-! An eight-bit tail-tested activation with a selectable increment. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

abbrev Byte := BitVec 8
abbrev word : ValueSort Unit := .data ()

inductive Op : Signature Unit where
  | advance (amount : Byte) : Op [word] word
  | continues : Op [word, .predicate] .predicate

def model : Model Op where
  value := fun _ => Byte
  run
    | .advance amount, .cons old .nil => BitVec.add old amount
    | .continues, .cons next (.cons enabled .nil) =>
      ⟨enabled.down && BitVec.ult next 3⟩

instance wordEq : BankDecidableEq model.value (dataPorts [ValueSort.data ()]) where
  atPort i := Fin.cases (motive := fun j => DecidableEq (Val model.value (dataPorts [word])[j]))
    (inferInstance : DecidableEq Byte) (fun j => j.elim0) i

abbrev HeaderSigs : List (List (Ty Unit)) := [[.value word], [.value .predicate]]

/-- The guard tests the updated word. Both successors use that same
updated producer, either as feedback or as the returned value. -/
def graph (amount : Byte) : Program Op [word, .predicate] () [] HeaderSigs word where
  preheader := .nil
  header :=
    .cons (.advance amount) (.cons (.arg (.tail (.tail .head))) .nil)
      (.cons .continues (.cons (.output ⟨0, by decide⟩ .head) (.cons (.arg (.tail .head)) .nil)) .nil)
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output ⟨0, by decide⟩ .head) .nil
  predicate := .output ⟨1, by decide⟩ .head
  result := .output ⟨0, by decide⟩ .head

def facts (start : Byte) (enabled : Flat (ULift Bool)) : Tuple (Fact model.value) (dataPorts [word, .predicate]) :=
  .cons (.constant start) (.cons enabled .nil)

def entry (start : Byte) (enabled : Bool) : Tuple (Val model.value) (dataPorts [word, .predicate]) :=
  .cons start (.cons ⟨enabled⟩ .nil)

/-- Entry, backedge, and exit marks, followed by the latch and exit facts. -/
def report (amount : Byte) (enabled : Flat (ULift Bool)) : Bool × Bool × Bool × Flat Nat × Flat Nat :=
  let state := solve model (graph amount) (facts 0 enabled)
  (decide (incomingIndex .entry ∈ state.1), decide (incomingIndex .backedge ∈ state.1),
    decide (exitIndex ∈ state.1), (state.2.1 (0 : Fin 1)).map BitVec.toNat, state.2.2.map BitVec.toNat)

/-- Inspect the latch after a given number of simultaneous analysis rounds.
This counter concerns transfer iteration, independently of concrete execution. -/
def changingLatch (rounds : Nat) : Flat Nat :=
  let state := (transfer model (graph 1) (facts 0 (.constant ⟨true⟩)))^[rounds] ⊥
  (state.2.1 (0 : Fin 1)).map BitVec.toNat

def run (amount : Byte) (enabled : Bool) (backedges : Nat) : Option Nat :=
  ((graph amount).evalBackedges model backedges (entry 0 enabled)).map BitVec.toNat

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example
