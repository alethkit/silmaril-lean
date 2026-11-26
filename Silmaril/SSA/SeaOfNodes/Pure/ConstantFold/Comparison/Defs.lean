module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs

/-! Simple chapter 8's word equality and signed ordering in the native
predicate sort. Arithmetic uses the existing word profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison

open Diamond (Model Signature ValueSort)
open SubZero (word)

/-- Arithmetic and the three two-word comparisons implemented by `BoolNode`. -/
inductive Opcode : Signature Unit where
  | arithmetic {ins out} (op : SubZero.Opcode ins out) : Opcode ins out
  | boolean (value : Bool) : Opcode [] .predicate
  | eq : Opcode [word, word] .predicate
  | slt : Opcode [word, word] .predicate
  | sle : Opcode [word, word] .predicate

def model : Model Opcode where
  value := SubZero.model.value
  run
    | .arithmetic op, inputs => SubZero.model.run op inputs
    | .boolean value, .nil => ⟨value⟩
    | .eq, .cons lhs (.cons rhs .nil) => ⟨BEq.beq (α := BitVec 64) lhs rhs⟩
    | .slt, .cons lhs (.cons rhs .nil) => ⟨lhs.slt rhs⟩
    | .sle, .cons lhs (.cons rhs .nil) => ⟨lhs.sle rhs⟩

def rules : Scan.Rules model :=
  fun op => match op with
  | .arithmetic arith =>
    match arithmeticRules arith with
    | .literal original => .literal (Opcode.arithmetic original)
    | .binary opcode encode read_encode =>
      .binary (Opcode.arithmetic opcode) (fun value => Opcode.arithmetic (encode value)) read_encode
  | .boolean value => .literal (Opcode.boolean value)
  | .eq => .binary Opcode.eq (fun value => Opcode.boolean value.down) (fun _ => rfl)
  | .slt => .binary Opcode.slt (fun value => Opcode.boolean value.down) (fun _ => rfl)
  | .sle => .binary Opcode.sle (fun value => Opcode.boolean value.down) (fun _ => rfl)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Fold explicit literal arithmetic and comparisons in dependency order. -/
def fold (program : Program Opcode inputs out) : Program Opcode inputs out :=
  Scan.fold rules program

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison
