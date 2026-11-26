module

public import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs

/-! Fold Simple's same-source subtraction to a zero literal in its typed slot. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SubSelf

open Diamond (Dataflow Ty ValueSort)
open GVN (Producer)
open SubZero (operands? word)

variable {args : List (Ty Unit)}

/-- Replace a nominated word binding while preserving its slot and every
other binding. The operand check in `fold?` justifies this edit. -/
def replaceWithZero :
    {past sigs : List (List (Ty Unit))} → {flow : Dataflow SubZero.Opcode args past sigs} →
      Producer flow word → Dataflow SubZero.Opcode args past sigs
  | _, _, _, .here (rest := rest) => .cons (.literal 0) .nil rest
  | _, _, _, .later (op := op) (inputs := inputs) ref => .cons op inputs (replaceWithZero ref)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Fold a subtraction only when its two ordered operands have the same
typed origin in the binding's actual prefix. -/
def fold? (program : Program SubZero.Opcode inputs out) (candidate : Producer program.dataflow word) :
    Option (Program SubZero.Opcode inputs out) :=
  (operands? candidate).bind fun (lhs, rhs) =>
    if lhs.address = rhs.address then some { program with dataflow := replaceWithZero candidate }
    else none

/-- Apply the first accepted fold in the existing word-producer enumeration. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Program SubZero.Opcode inputs out) :=
  (RightIdentityPass.wordProducers program.dataflow).findSome? (fold? program)

end Silmaril.SSA.SeaOfNodes.Pure.SubSelf
