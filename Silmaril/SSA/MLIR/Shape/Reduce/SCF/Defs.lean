module

public import Silmaril.SSA.MLIR.SCF.For.Defs
public import Silmaril.SSA.MLIR.Shape.Reduce.Defs

/-! # Lower concrete pure Shape reduction to the checked SCF loop -/

@[expose] public section

namespace Silmaril.MLIR.Shape.ReduceBody

open Arith (Width Var Env)
open _root_.Silmaril.MLIR.Pure (Code Eval Operands OpSignature)
open _root_.Silmaril.MLIR.SCF (For Yield)

variable {Op : OpSignature} {indexWidth : Width} {Carried Captures Γ Δ : List Width}

/-- The specialized SCF body uses an immutable table of the encoded extents. -/
def extentTable (indexWidth : Width) (shape : ExtentTensor) : Array (BitVec indexWidth.val) :=
  Array.ofFn fun axis : Fin shape.1 => BitVec.ofNat indexWidth.val (shape.2 (axis, ()))

inductive ForOp (Op : OpSignature) (indexWidth : Width) : OpSignature where
  | original {args : List Width} {result : Width} (op : Op args result) : ForOp Op indexWidth args result
  | lookup (table : Array (BitVec indexWidth.val)) : ForOp Op indexWidth [indexWidth] indexWidth

/-- The lookup primitive is total, as required by `Pure.Eval`. The lowering
only observes it on table indices for which the lookup succeeds. -/
def forEval (evalOp : Eval Op) : Eval (ForOp Op indexWidth)
  | _, _, .original op, args => evalOp op args
  | _, _, .lookup table, .cons axis .nil => table[axis.toNat]?.getD 0

/-- The enclosing input supplies zero, rank, step, initial carry, and captures. -/
abbrev ForInputs (indexWidth : Width) (Carried Captures : List Width) :=
  indexWidth :: indexWidth :: indexWidth :: (Carried ++ Captures)

def lowerInput (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) :
    Env (ForInputs indexWidth Carried Captures) :=
  .cons 0 (.cons (BitVec.ofNat indexWidth.val shape.1) (.cons 1 (initial.append captures)))

/-- Preserve a prefix of local variables when renaming the enclosing scope. -/
def liftRename (rename : ∀ {w}, Var Γ w → Var Δ w) :
    (locals : List Width) → ∀ {w}, Var (locals ++ Γ) w → Var (locals ++ Δ) w
  | [], _, ref => rename ref
  | _ :: _, _, .here => .here
  | _ :: rest, _, .there ref => .there (liftRename rename rest ref)

/-- Copy the straight-line operations, rename their operand references, and
turn the Shape terminator tuple into an SCF yield. -/
def lowerCode : {Γ Δ : List Width} → Code Op (fun scope => Operands scope Carried) Γ →
    (∀ {w}, Var Γ w → Var Δ w) → Code (ForOp Op indexWidth) (Yield Carried) Δ
  | _, _, .terminator values, rename => .terminator (.yield (For.renameOperands rename values))
  | _, _, .letOp op args rest, rename =>
    .letOp (.original op) (For.renameOperands rename args) (lowerCode rest (liftRename rename [_]))

/-- The lookup binds the extent in front of the induction variable. Original
captures skip the loop bounds and original initial operands in parent scope. -/
def lowerBodyRef : ∀ {w}, Var (indexWidth :: indexWidth :: (Carried ++ Captures)) w →
    Var (indexWidth :: indexWidth :: (Carried ++ ForInputs indexWidth Carried Captures)) w
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there ref) => .there (.there (liftRename
      (fun v => For.weakenVar v (indexWidth :: indexWidth :: indexWidth :: Carried)) Carried ref))

/-- Emit `scf.for` over `[0, rank)` with step one. Each trip looks up the
extent before invoking the copied body. The continuation returns the carry. -/
def lowerToFor (body : ReduceBody Op indexWidth Carried Captures) (shape : ExtentTensor)
    (widthSupported : indexWidth.val ≤ 2 ^ 24 - 1) :
    For (ForOp Op indexWidth) (ForInputs indexWidth Carried Captures) Carried where
  width := indexWidth
  widthSupported := widthSupported
  Carried := Carried
  lowerBound := .here
  upperBound := .there .here
  step := .there (.there .here)
  init := For.renameOperands (fun v => .there (.there (.there v)))
    (For.argumentOperands Captures Carried)
  body := .letOp (.lookup (extentTable indexWidth shape)) (.cons .here .nil)
    (lowerCode body lowerBodyRef)
  cont := .terminator (.ret (For.argumentOperands (ForInputs indexWidth Carried Captures) Carried))

/-- Check the source admission and the target width bound before running SCF. -/
def runLowered? (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) : Option (Env Carried) :=
  if supported : indexWidth.val ≤ 2 ^ 24 - 1 then
    if shape.ReduceFits indexWidth then
      (body.lowerToFor shape supported).run (forEval evalOp)
        (lowerInput (indexWidth := indexWidth) shape initial captures)
    else none
  else none

end Silmaril.MLIR.Shape.ReduceBody
