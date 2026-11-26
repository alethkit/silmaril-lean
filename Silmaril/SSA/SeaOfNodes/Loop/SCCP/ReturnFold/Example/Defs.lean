module

public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Thms

/-! Add a literal to the opcode profile of the existing SCCP loop fixture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example

open Diamond (Model Signature ValueSort dataPorts)
open SCCP.Example (Byte word HeaderSigs)
open Semantics.Dataflow (Flat)

inductive Opcode : Signature Unit where
  | original {ins : List (ValueSort Unit)} {out : ValueSort Unit} :
      SCCP.Example.Op ins out → Opcode ins out
  | literal : Byte → Opcode [] word

def model : Model Opcode where
  value := SCCP.Example.model.value
  run
    | .original op, args => SCCP.Example.model.run op args
    | .literal value, .nil => value

instance wordEq : BankDecidableEq model.value (dataPorts [ValueSort.data ()]) :=
  SCCP.Example.wordEq

def literals : Literals model word where
  opcode := Opcode.literal
  run_opcode _ := rfl

/-- Reuse the native eight-bit loop and retain its typed wires. -/
def graph (amount : Byte) : Program Opcode [word, .predicate] () [] HeaderSigs word :=
  Loop.Institution.mapGraph (P := ⟨SCCP.Example.Op⟩) (Q := ⟨Opcode⟩)
    ⟨fun op => .original op⟩ (SCCP.Example.graph amount)

abbrev Target := Graph Opcode [word, .predicate] [word] [] (HeaderSigs ++ [[.value word]]) word

def fold (amount : Byte) (enabled : Flat (ULift Bool)) : Except Refusal Target :=
  rewrite model (graph amount) (SCCP.Example.facts 0 enabled) literals

/-- The producer index of the rewritten result. The literal follows the
original update and guard producers at indices 0 and 1. -/
def resultProducer (amount : Byte) (enabled : Flat (ULift Bool)) : Except Refusal (Option Nat) :=
  (fold amount enabled).map fun rewritten => rewritten.result.producer

def run (amount : Byte) (enabled : Flat (ULift Bool)) (test : Bool) (budget : Nat) :
    Except Refusal (Option Nat) :=
  (fold amount enabled).map fun rewritten =>
    (rewritten.evalBackedges model budget (SCCP.Example.entry 0 test)).map BitVec.toNat

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example
