module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs

/-! The direct two-Φ case of Simple chapter 8's AddNode.phiCon.
The two operands are columns of one native join row, with one row per predecessor. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair

open Pure.ConstantFold (Literals)
open Pure.ConstantFold.Scan (literalInputs?)
open Pure.SubZero (model word)
open RVSDG (Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}

abbrev Source (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) :=
  Arms.Graph Pure.SubZero.Opcode inputs sigs [word, word]

abbrev Operands := Tuple (Val model.value) (dataPorts [word, word])

abbrev add (operands : Operands) : BitVec 64 := model.run .add operands

/-- The original candidate adds both values read at this predecessor occurrence. -/
def sourceAt (g : Source inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (slot : Slot) : BitVec 64 :=
  add ((g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit))

def sourceDenote (g : Source inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs)) : BitVec 64 :=
  add (g.denote model entry)

/-- Compose the native join's finite observation with one nominated return add. -/
def SourceReturns (g : Source inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (result : BitVec 64) : Prop :=
  ∃ operands, g.Returns model entry operands ∧ add operands = result

/-- Recover both actual join operands in this arm's typed scope. -/
def armLiterals? (known : Literals args past) (arm : Arms.Arm Pure.SubZero.Opcode args past [word, word]) :
    Option Operands :=
  literalInputs? (scanLiterals known arm.dataflow) arm.outputs

/-- Each Φ must be nonconstant as a whole. At least one occurrence must
distinguish the columns by value, which rules out the earlier same-node add. -/
def eligible (first second : Operands) : Bool :=
  let firstLeft : BitVec 64 := first.get .head
  let firstRight : BitVec 64 := first.get (.tail .head)
  let secondLeft : BitVec 64 := second.get .head
  let secondRight : BitVec 64 := second.get (.tail .head)
  decide (firstLeft ≠ secondLeft ∧ firstRight ≠ secondRight ∧
    (firstLeft ≠ firstRight ∨ secondLeft ≠ secondRight))

/-- Use the same Region and emit one folded word for each old predecessor. -/
def emit (g : Source inputs sigs) (first second : Operands) : Result inputs sigs where
  shared := g.shared
  predicate := g.predicate
  merge := g.merge
  arms
    | .first => literalArm (add first)
    | .second => literalArm (add second)

/-- The input type supplies the one complete Region and both columns at
each slot. Check all four word literals and the earlier add cases. -/
def rewrite? (g : Source inputs sigs) : Option (Result inputs sigs) := do
  let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
  let first ← armLiterals? known (g.arms .first)
  let second ← armLiterals? known (g.arms .second)
  if eligible first second then some (emit g first second) else none

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair
