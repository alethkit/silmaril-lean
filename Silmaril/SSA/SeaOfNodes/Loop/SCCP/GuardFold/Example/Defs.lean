module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Thms

/-! Specialize an external guard and reject a guard that varies across activations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example

open Diamond (Model Signature Ty ValueSort dataPorts)
open SCCP.Example (word entry facts)
open ReturnFold (Literals Refusal)
open Semantics.Dataflow (Flat)

inductive Opcode : Signature Unit where
  | original {ins : List (ValueSort Unit)} {out : ValueSort Unit} :
      ReturnFold.Example.Opcode ins out → Opcode ins out
  | test (value : Bool) : Opcode [] .predicate

def model : Model Opcode where
  value := ReturnFold.Example.model.value
  run
    | .original op, args => ReturnFold.Example.model.run op args
    | .test value, .nil => ⟨value⟩

instance wordEq : BankDecidableEq model.value (dataPorts [ValueSort.data ()]) :=
  ReturnFold.Example.wordEq

def literals : Literals model .predicate where
  opcode value := .test value.down
  run_opcode := fun ⟨_⟩ => rfl

def relabel {sigs : List (List (Ty Unit))}
    (source : Program ReturnFold.Example.Opcode [word, .predicate] () [] sigs word) :
    Program Opcode [word, .predicate] () [] sigs word :=
  Loop.Institution.mapGraph (P := ⟨ReturnFold.Example.Opcode⟩) (Q := ⟨Opcode⟩)
    ⟨fun op => .original op⟩ source

abbrev HeaderSigs := FeedbackFold.Example.HeaderSigs

def graph : Program Opcode [word, .predicate] () [] HeaderSigs word :=
  relabel FeedbackFold.Example.graph

def fold (guard : Flat (ULift Bool)) :
    Except Refusal (Program Opcode [word, .predicate] () [] (HeaderSigs ++ [[.value .predicate]]) word) :=
  rewrite model graph (facts 0 guard) literals

def predicateProducer (guard : Flat (ULift Bool)) : Except Refusal (Option Nat) :=
  (fold guard).map fun rewritten => rewritten.predicate.producer

def run (test : Bool) (budget : Nat) : Except Refusal (Option Nat) :=
  (fold (.constant ⟨test⟩)).map fun rewritten =>
    (rewritten.evalBackedges model budget (entry 0 test)).map BitVec.toNat

/-- The increment-one loop starts with a true test and exits on a later
activation, so its fixed-point guard cannot be specialized. -/
def varyingGuard : Except Refusal (Option Nat) :=
  (rewrite model (relabel (ReturnFold.Example.graph 1)) (facts 0 (.constant ⟨true⟩)) literals).map
    fun rewritten => rewritten.predicate.producer

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Example
