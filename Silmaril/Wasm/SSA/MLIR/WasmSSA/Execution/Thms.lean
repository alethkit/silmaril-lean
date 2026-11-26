module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution

public section

namespace Silmaril.MLIR.WasmSSA

open Silmaril.Wasm (TypeIdx)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Context Expand)

/-- With typed arguments and a local layout that fits, the emitted Core body
has a run from the standard call frame to the evaluated source word followed
by `return`. The run preserves the store for every profile and host relation. -/
theorem Func.toWasm_returns {H : Type} {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits)
    (args : Env params) (m : ModuleInst) (P : Profile) (host : HostSemantics H) (s : Store H) :
    ∃ final, Steps P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s, final, vals [result.toVal (f.eval args)] ++ [.plain .return_]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_returns f C type fits args m P host s

/-- If the store holds an instance of the lowered code with the declared
signature, a Core invocation can finish with exactly the evaluated source word
and the original store. -/
theorem Func.toWasm_invoke {H : Type} {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (P : Profile) (host : HostSemantics H) (s : Store H) (addr : Nat) (fi : FuncInst H)
    (lookup : s.funcs[addr]? = some fi) (code : fi.code = .wasm (f.toWasm C type fits))
    (signature : Expand fi.type (Func.coreSignature params result)) :
    Steps P host (invoke s addr args.toWasmArgs) ⟨s, {}, vals [result.toVal (f.eval args)]⟩ :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_invoke f C type fits args P host s addr fi lookup code signature

end Silmaril.MLIR.WasmSSA
