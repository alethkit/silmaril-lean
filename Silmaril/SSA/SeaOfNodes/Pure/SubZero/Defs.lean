module

public import Silmaril.SSA.SeaOfNodes.Pure.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs

/-!
# One checked `x - 0 → x` idealization

The restricted integer profile follows Simple chapter 8's Java long
arithmetic. The right operand must name the actual typed literal-zero
producer. Erasure routes uses of the subtraction to its left operand.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SubZero

open Diamond (Dataflow Model Signature Ty ValueSort)
open GVN (Producer)
open GVN.Elimination (erase inFinal operandScope)
open RVSDG (Origin)

abbrev word : ValueSort Unit := .data ()
abbrev wordPort : Ty Unit := .value word

/-- The integer fragment needed for the checked identity. -/
inductive Opcode : Signature Unit where
  | literal (value : BitVec 64) : Opcode [] word
  | sub : Opcode [word, word] word

def model : Model Opcode where
  value _ := BitVec 64
  run
    | .literal value, .nil => value
    | .sub, .cons lhs (.cons rhs .nil) => BitVec.sub lhs rhs

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {flow : Dataflow Opcode args past sigs}

/-- Recover the ordered operand wires in the actual subtraction prefix. -/
def operands? :
    {past sigs : List (List (Ty Unit))} → {flow : Dataflow Opcode args past sigs} →
      {sort : ValueSort Unit} → (candidate : Producer flow sort) →
        Option (Origin args (operandScope candidate) wordPort × Origin args (operandScope candidate) wordPort)
  | _, _, _, _, .here (op := .sub) (inputs := .cons lhs (.cons rhs .nil)) => some (lhs, rhs)
  | _, _, _, _, .here (op := .literal _) => none
  | _, _, _, _, .later next => operands? next

/-- Only an explicit word-zero literal can witness the right operand. -/
def isZero (candidate : Producer flow word) : Bool :=
  match candidate.key with
  | ⟨_, .literal value, _⟩ => decide (value = 0)
  | ⟨_, .sub, _⟩ => false

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Erase the subtraction and reindex all surviving uses and the return wire. -/
def rewrite? (program : Program Opcode inputs out)
    (candidate zero : Producer program.dataflow word) : Option (Program Opcode inputs out) :=
  (operands? candidate).bind fun (lhs, rhs) =>
    if isZero zero && decide ((inFinal candidate rhs).address = zero.origin.address) then
      let result := erase candidate lhs
      some { dataflow := result.flow, result := result.route program.result }
    else none

end Silmaril.SSA.SeaOfNodes.Pure.SubZero
