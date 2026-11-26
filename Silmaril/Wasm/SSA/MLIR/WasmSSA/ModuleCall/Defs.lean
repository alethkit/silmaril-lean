module

public import Silmaril.SSA.MLIR.Module.Symbols.Defs
public import Silmaril.Wasm.Instructions

/-! # Direct call emission in a function index space with no imports -/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA.ModuleCall

universe u v

/-- The declaration's position as a Core function index, if it fits in `u32`.
The Core module must emit functions in this order and have no function imports. -/
def symbolIndex? {F : Type u} (symbols : MLIR.Module F) (name : String) : Option Wasm.FuncIdx :=
  (symbols.funcs.findIdx? (fun entry => name == entry.1)).bind Wasm.Idx.ofNat?

/-- Lower the callee of an admitted call into the closed function index space. -/
def callIndex? {I : Type u} {O : Type v} {symbols : MLIR.Module (FuncSignature I O)}
    {inputs : I} {outputs : O} (call : DirectCall symbols inputs outputs) : Option Wasm.FuncIdx :=
  symbolIndex? symbols call.callee

/-- Admit a symbolic call site and emit its single Core `call` instruction.
The caller separately supplies the operand stack at the checked profile. -/
def emitCall? {I : Type u} {O : Type v} [DecidableEq I] [DecidableEq O]
    (symbols : MLIR.Module (FuncSignature I O)) (callee : String) (inputs : I) (outputs : O) :
    Option Wasm.Instr := do
  let call ← DirectCall.resolve? symbols callee inputs outputs
  (callIndex? call).map Wasm.Instr.call

end Silmaril.MLIR.WasmSSA.ModuleCall
