module

public import Silmaril.SSA.MLIR.WasmSSA.Eval.Defs
public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation

/-! The argument and result encodings for observing a lowered WasmSSA function. -/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA

open Silmaril.Wasm.Execution.Core (Val)

def IntType.toVal : (t : IntType) → BitVec t.width → Val
  | .i32, word => .i32 word
  | .i64, word => .i64 word

def Env.toWasmArgs {ts : List IntType} : Env ts → List Val
  | .nil => []
  | .cons (t := t) word tail => t.toVal word :: tail.toWasmArgs

end Silmaril.MLIR.WasmSSA
