module

public import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Defs

/-! Fold binary operations whose actual operands are word literals in the
current prefix. A replacement occupies the original typed result slot. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN.Elimination (splitOrigin)
open SubZero (BinaryOpcode model word)
open RVSDG (Origin Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}

/-- A typed lookup of explicit literal values in the rewritten prefix. -/
abbrev Literals (args : List (Ty Unit)) (past : List (List (Ty Unit))) :=
  ∀ {t : Ty Unit}, Origin args past t → Option (Val model.value t)

/-- Extend the lookup along the existing typed origin split. -/
def Literals.push (known : Literals args past) (value : Option (Val model.value (.value out))) :
    Literals args (past ++ [[.value out]]) :=
  fun wire =>
    match splitOrigin (T := Ty Unit) (past := past) [.value out] wire with
    | .inl earlier => known earlier
    | .inr .head => value
    | .inr (.tail port) => nomatch port

/-- Compute the replacement payload with the same operator evaluator as
native execution. Both ordered wires must resolve to literals. -/
def binaryLiteral? (known : Literals args past) (op : BinaryOpcode)
    (operands : Wires args past (dataPorts [word, word])) : Option (SubZero.Opcode [] word) :=
  match operands with
  | .cons lhs (.cons rhs .nil) =>
    (known lhs).bind fun x =>
      (known rhs).map fun y => .literal (model.run op (.cons x (.cons y .nil)))

/-- Recognize literals and fold the supported binary opcodes. -/
def literal? (known : Literals args past) (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)) : Option (SubZero.Opcode [] out) :=
  match op with
  | .literal value => some (.literal value)
  | .add => binaryLiteral? known .add operands
  | .sub => binaryLiteral? known .sub operands
  | .mul => binaryLiteral? known .mul operands

/-- Scan once in dependency order. Preserve every output signature, so the
suffix's typed origins and the program return need no renumbering. -/
def foldDataflow : {past sigs : List (List (Ty Unit))} →
    Literals args past → Dataflow SubZero.Opcode args past sigs → Dataflow SubZero.Opcode args past sigs
  | _, _, _, .nil => .nil
  | _, _, known, .cons op operands rest =>
    match literal? known op operands with
    | some literal => .cons literal .nil (foldDataflow (known.push (some (model.run literal .nil))) rest)
    | none => .cons op operands (foldDataflow (known.push none) rest)

variable {inputs : List (ValueSort Unit)}

/-- Fold the native program with no assumptions about its arguments. -/
def fold (program : Program SubZero.Opcode inputs out) : Program SubZero.Opcode inputs out :=
  { program with dataflow := foldDataflow (fun _ => none) program.dataflow }

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
