module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Defs

/-! Source-ordered entry point for the nominated rotated two-Φ add. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch

open Pure.ConstantFold (Literals)
open Pure.SubZero (model word)
open RVSDG (Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

inductive Refusal where
  | constantColumnPriority
  | nonliteralOperand
  deriving DecidableEq, Repr

/-- Each success carries the actual native program for that source outcome. -/
inductive Result (inputs : List (ValueSort Unit)) (sigs : List (List (Ty Unit))) where
  | residualPhi (program : Program inputs sigs [word])
  | constantAdd (program : Program inputs sigs [])
  | captureOnly (program : Program inputs sigs [])

def Result.denote (result : Result inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    BitVec 64 :=
  match result with
  | .residualPhi p => p.denote entry
  | .constantAdd p | .captureOnly p => p.denote entry

def Result.Returns (result : Result inputs sigs) (entry : Tuple (Val model.value) (dataPorts inputs))
    (value : BitVec 64) : Prop :=
  match result with
  | .residualPhi p => p.Returns entry value
  | .constantAdd p | .captureOnly p => p.Returns entry value

/-- Check priority even when a nonliteral in the other column prevented
the full row lookup. -/
def hasConstantColumn (g : AddPhi.Pair.Source inputs sigs) : Bool :=
  let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
  let armWords (arm : Arms.Arm Pure.SubZero.Opcode (dataPorts inputs) (extend [] sigs) [word, word]) :
      Option (BitVec 64) × Option (BitVec 64) :=
    let facts : Literals (dataPorts inputs) (extend (extend [] sigs) arm.sigs) :=
      scanLiterals known arm.dataflow
    (facts (arm.outputs.get .head), facts (arm.outputs.get (.tail .head)))
  let sameLiteral : Option (BitVec 64) → Option (BitVec 64) → Bool := fun
    | some first, some second => first == second
    | _, _ => false
  let (firstLeft, firstRight) := armWords (g.arms .first)
  let (secondLeft, secondRight) := armWords (g.arms .second)
  sameLiteral firstLeft secondLeft || sameLiteral firstRight secondRight

/-- Classify the materialization and the immediate right-zero follow-up. -/
def emit (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs)
    (first second : AddPhi.Pair.Operands) : Result inputs sigs :=
  let value := AddPhi.Pair.add first
  if value = AddPhi.Pair.add second then
    if value = 0 then .captureOnly (Collapse.emit g x value)
    else .constantAdd (Collapse.emit g x value)
  else .residualPhi (Rotate.emit x (AddPhi.Pair.emit g first second))

/-- Original column materialization takes precedence over the rotated
rule. The successful path shares one lookup of the ordered literal rows. -/
def rewrite (g : AddPhi.Pair.Source inputs sigs) (x : InputWord inputs) :
    Except Refusal (Result inputs sigs) :=
  match AddPhi.Pair.literalRows? g with
  | none =>
    if hasConstantColumn g then .error .constantColumnPriority else .error .nonliteralOperand
  | some (first, second) =>
    if AddPhi.Pair.nonconstantColumns first second then .ok (emit g x first second)
    else .error .constantColumnPriority

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch
