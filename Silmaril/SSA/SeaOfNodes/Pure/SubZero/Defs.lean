module

public import Silmaril.SSA.SeaOfNodes.Pure.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs

/-!
# Checked right identities for the Simple word profile

The restricted integer profile follows Simple chapter 8's Java long
arithmetic. The actual right operand must name the selected identity
literal. Erasure routes uses of the binding to its left operand.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SubZero

open Diamond (Dataflow Model Signature Ty ValueSort)
open GVN (Producer)
open GVN.Elimination (erase inFinal operandScope)
open RVSDG (Origin)

abbrev word : ValueSort Unit := .data ()
abbrev wordPort : Ty Unit := .value word

/-- The literal and binary integer fragment for the checked identities. -/
inductive Opcode : Signature Unit where
  | literal (value : BitVec 64) : Opcode [] word
  | sub : Opcode [word, word] word
  | add : Opcode [word, word] word
  | mul : Opcode [word, word] word

def model : Model Opcode where
  value _ := BitVec 64
  run
    | .literal value, .nil => value
    | .sub, .cons lhs (.cons rhs .nil) => BitVec.sub lhs rhs
    | .add, .cons lhs (.cons rhs .nil) => BitVec.add lhs rhs
    | .mul, .cons lhs (.cons rhs .nil) => BitVec.mul lhs rhs

abbrev BinaryOpcode := Opcode [word, word] word

instance : DecidableEq BinaryOpcode := fun lhs rhs => by
  cases lhs <;> cases rhs <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- The right-hand literal required by the selected binary opcode. -/
def rightIdentity : BinaryOpcode → BitVec 64
  | .sub | .add => 0
  | .mul => 1

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {flow : Dataflow Opcode args past sigs}

/-- Recover the ordered operand wires in the actual prefix for the selected opcode. -/
def operandsFor? (opcode : BinaryOpcode) :
    {past sigs : List (List (Ty Unit))} → {flow : Dataflow Opcode args past sigs} →
      {sort : ValueSort Unit} → (candidate : Producer flow sort) →
        Option (Origin args (operandScope candidate) wordPort × Origin args (operandScope candidate) wordPort)
  | _, _, _, _, .here (op := .sub) (inputs := .cons lhs (.cons rhs .nil)) =>
    if opcode = .sub then some (lhs, rhs) else none
  | _, _, _, _, .here (op := .add) (inputs := .cons lhs (.cons rhs .nil)) =>
    if opcode = .add then some (lhs, rhs) else none
  | _, _, _, _, .here (op := .mul) (inputs := .cons lhs (.cons rhs .nil)) =>
    if opcode = .mul then some (lhs, rhs) else none
  | _, _, _, _, .here (op := .literal _) => none
  | _, _, _, _, .later next => operandsFor? opcode next

/-- Only an explicit word literal of the required value can witness the right operand. -/
def isLiteral (expected : BitVec 64) (candidate : Producer flow word) : Bool :=
  match candidate.key with
  | ⟨_, .literal value, _⟩ => decide (value = expected)
  | ⟨_, .sub, _⟩ | ⟨_, .add, _⟩ | ⟨_, .mul, _⟩ => false

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Erase the accepted binding and reindex all surviving uses and the return wire. -/
def rewriteRightIdentity? (opcode : BinaryOpcode) (program : Program Opcode inputs out)
    (candidate literal : Producer program.dataflow word) : Option (Program Opcode inputs out) :=
  (operandsFor? opcode candidate).bind fun (lhs, rhs) =>
    if isLiteral (rightIdentity opcode) literal &&
        decide ((inFinal candidate rhs).address = literal.origin.address) then
      let result := erase candidate lhs
      some { dataflow := result.flow, result := result.route program.result }
    else none

/-- Recover the ordered operand wires in the actual subtraction prefix. -/
abbrev operands? {sort : ValueSort Unit} (candidate : Producer flow sort) :=
  operandsFor? .sub candidate

/-- Only an explicit word-zero literal can witness the right operand. -/
abbrev isZero (candidate : Producer flow word) := isLiteral 0 candidate

/-- Erase a subtraction by zero. -/
abbrev rewrite? (program : Program Opcode inputs out)
    (candidate zero : Producer program.dataflow word) :=
  rewriteRightIdentity? .sub program candidate zero

end Silmaril.SSA.SeaOfNodes.Pure.SubZero
