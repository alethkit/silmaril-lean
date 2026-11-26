module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Defs
public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Examples.Thms
public import Silmaril.Wasm.Execution.Core.Exec.ConstEval
public import Silmaril.Wasm.Execution.Core.Exec.Instantiate
public import Silmaril.Wasm.Validation.Check.Validate

/-! A closed module with an exported wrapper and one later WasmSSA leaf. -/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA.ModuleCall.Examples

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (CModuleType validate?)

abbrev Params : List IntType := [.i64, .i64]

def declared : MLIR.Module (FuncSignature (List IntType) IntType) where
  funcs := [("run", ⟨Params, .i64⟩), ("select_difference", ⟨Params, .i64⟩)]
  uniqueNames := by decide

/-- The two forms of body in this fixture, both at its single integer profile. -/
inductive Body : List IntType → IntType → Type where
  | forward : DirectCall declared Params .i64 → Body Params .i64
  | leaf : Func Params .i64 → Body Params .i64

def site : DirectCall declared Params .i64 :=
  (DirectCall.resolve? declared "select_difference" Params .i64).get (by decide)

def source : FuncModule Body where
  funcs := [("run", ⟨Params, .i64, .forward site⟩),
    ("select_difference", ⟨Params, .i64, .leaf WasmSSA.Examples.selectDifference⟩)]
  uniqueNames := declared.uniqueNames

/-- Both fixture functions use the module's sole type entry. -/
def Body.toWasm? {inputs output} : Body inputs output → Option Wasm.Func
  | .forward call => (callIndex? call).map fun idx =>
      ⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .call idx, .return_]⟩
  | .leaf fn => fn.toWasm? WasmSSA.Examples.context ⟨0⟩

/-- Emit in source declaration order and export the wrapper by its symbol. -/
def emitModule? : Option Wasm.Module := do
  let funcs ← source.funcs.mapM fun entry => entry.2.body.toWasm?
  let wrapper ← symbolIndex? source.signatures "run"
  return {
    types := [⟨[⟨true, [], .func ⟨Params.map IntType.valType, [IntType.i64.valType]⟩⟩]⟩]
    funcs := funcs
    exports := [⟨"run", .func wrapper⟩] }

def coreModule : Wasm.Module := emitModule?.get (by decide)

def checkedType : CModuleType := (validate? coreModule).get (by decide)

/-- Compute the Core configuration by instantiating from the empty store. -/
def instantiated : Config Empty :=
  (instantiate? evalConst? ({} : Store Empty) coreModule []).get (by decide)

def wrapperIndex : Wasm.FuncIdx := (symbolIndex? source.signatures "run").get (by decide)

def leafIndex : Wasm.FuncIdx := (callIndex? site).get (by decide)

def wrapperAddress : Nat := (instantiated.frame.module.funcs[wrapperIndex.toNat]?).get (by decide)

def leafAddress : Nat := (instantiated.frame.module.funcs[leafIndex.toNat]?).get (by decide)

def wrapperInstance : FuncInst Empty := (instantiated.store.funcs[wrapperAddress]?).get (by decide)

def leafInstance : FuncInst Empty := (instantiated.store.funcs[leafAddress]?).get (by decide)

def wrapperCode : Wasm.Func := coreModule.funcs[wrapperIndex.toNat]'(by decide)

def args (x y : BitVec 64) : Env Params := .cons x (.cons y .nil)

def result (x y : BitVec 64) : Val :=
  .i64 (WasmSSA.Examples.selectDifference.eval (args x y))

end Silmaril.MLIR.WasmSSA.ModuleCall.Examples
