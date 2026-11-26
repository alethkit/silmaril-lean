module

public import Silmaril.SSA.MLIR.Pure.Defs
public import Silmaril.SSA.MLIR.Shape.Defs

/-! # Pure `shape.reduce` on concrete extent tensors

The scalar profile reserves one width for `index`. Other widths denote
signless integer types. The modeled body has one block with total primitives
and a single `shape.yield`, represented by its typed operand tuple.
-/

@[expose] public section

namespace Silmaril.MLIR.Shape

open Arith (Width Env)
open _root_.Silmaril.MLIR.Pure (Code Eval Operands OpSignature)

/-- The block receives the induction variable, the extent, and the carried
tuple, followed by any enclosing captures. Its yield has the carried types. -/
abbrev ReduceBody (Op : OpSignature) (indexWidth : Width) (Carried Captures : List Width) :=
  Code Op (fun scope => Operands scope Carried) (indexWidth :: indexWidth :: (Carried ++ Captures))

/-- The rank and each extent fit the nonnegative signed range of the chosen
`index` representation. Every induction value is then representable too. -/
def ExtentTensor.ReduceFits (shape : ExtentTensor) (indexWidth : Width) : Prop :=
  let bound := 2 ^ (indexWidth.val - 1)
  shape.1 < bound ∧ ∀ axis : Fin shape.1, shape.2 (axis, ()) < bound

instance instDecidableReduceFits (shape : ExtentTensor) (indexWidth : Width) :
    Decidable (shape.ReduceFits indexWidth) := by
  unfold ExtentTensor.ReduceFits
  infer_instance

namespace ReduceBody

variable {Op : OpSignature} {indexWidth : Width} {Carried Captures : List Width}

/-- Execute one single-block invocation and use the `shape.yield` operands as
the next carried tuple. The captures stay in their enclosing scope. -/
def step (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (axis extent : BitVec indexWidth.val) (carried : Env Carried) (captures : Env Captures) : Env Carried :=
  body.eval evalOp (fun yielded env => yielded.eval env)
    (.cons axis (.cons extent (carried.append captures)))

/-- The rank-bounded fold reads the extent at each axis in increasing order.
Use `run?` for the checked value model. -/
def denote (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) : Env Carried :=
  Fin.foldl shape.1 (fun carried axis =>
    body.step evalOp (BitVec.ofNat indexWidth.val axis.val)
      (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))) carried captures) initial

/-- Evaluate the fold when the rank and extents have a faithful `index`
encoding. An input outside that range is outside this profile. -/
def run? (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) : Option (Env Carried) :=
  if shape.ReduceFits indexWidth then some (body.denote evalOp shape initial captures) else none

end ReduceBody

end Silmaril.MLIR.Shape
