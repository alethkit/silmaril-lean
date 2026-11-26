module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs

/-! Simple chapter 8's word comparisons and Boolean negation in the
native predicate sort. Arithmetic uses the existing word profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison

open Diamond (Model Signature ValueSort)
open SubZero (word)

/-- Word arithmetic, the `BoolNode` comparisons, and negation of a Boolean. -/
inductive Opcode : Signature Unit where
  | arithmetic {ins out} (op : SubZero.Opcode ins out) : Opcode ins out
  | boolean (value : Bool) : Opcode [] .predicate
  | eq : Opcode [word, word] .predicate
  | slt : Opcode [word, word] .predicate
  | sle : Opcode [word, word] .predicate
  | not : Opcode [.predicate] .predicate

def model : Model Opcode where
  value := SubZero.model.value
  run
    | .arithmetic op, inputs => SubZero.model.run op inputs
    | .boolean value, .nil => ⟨value⟩
    | .eq, .cons lhs (.cons rhs .nil) => ⟨BEq.beq (α := BitVec 64) lhs rhs⟩
    | .slt, .cons lhs (.cons rhs .nil) => ⟨lhs.slt rhs⟩
    | .sle, .cons lhs (.cons rhs .nil) => ⟨lhs.sle rhs⟩
    | .not, .cons value .nil => ⟨!value.down⟩

def rules : Scan.Rules model :=
  fun op => match op with
  | .arithmetic arith => liftArithmeticRule (arithmeticRules arith)
  | .boolean value => .literal (Opcode.boolean value)
  | .eq => comparisonRule .eq true (by
    change ∀ value : BitVec 64, ULift.up (value == value) = ULift.up true
    intro value
    simp)
  | .slt => comparisonRule .slt false (by
    change ∀ value : BitVec 64, ULift.up (value.slt value) = ULift.up false
    intro value
    simp [BitVec.slt_eq_decide])
  | .sle => comparisonRule .sle true (by
    change ∀ value : BitVec 64, ULift.up (value.sle value) = ULift.up true
    intro value
    simp [BitVec.sle_eq_decide])
  | .not => .operation Opcode.not (fun value => Opcode.boolean value.down) (fun _ => rfl)
where
  liftArithmeticRule :
      {ins : List (ValueSort Unit)} → {out : ValueSort Unit} → {op : SubZero.Opcode ins out} →
        Scan.Rule SubZero.model op → Scan.Rule model (.arithmetic op)
    | _, _, _, .literal original => .literal (Opcode.arithmetic original)
    | _, _, _, .operation opcode encode read_encode =>
      .operation (Opcode.arithmetic opcode) (fun value => Opcode.arithmetic (encode value)) read_encode
    | _, _, _, .sameWord opcode result read_same fallback =>
      .sameWord (Opcode.arithmetic opcode) (.arithmetic result) read_same (liftArithmeticRule fallback)
  comparisonRule (op : Opcode [word, word] .predicate) (same : Bool)
      (read_same : ∀ value, model.run op (.cons value (.cons value .nil)) = ⟨same⟩) : Scan.Rule model op :=
    .sameWord op (.boolean same) read_same (.binary op (fun value => .boolean value.down) (fun _ => rfl))

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Fold literal operations and repeated-source comparisons in dependency order. -/
def fold (program : Program Opcode inputs out) : Program Opcode inputs out :=
  Scan.fold rules program

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison
