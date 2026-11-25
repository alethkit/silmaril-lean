module

import SqliteWasm.ThreadSetup

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand)
open SqliteWasm
open SqliteWasmArtifact (definedFunction?)

example :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      definedFunction? m 1516) = some threadSetupFunction ∧
    sqlite.functionSignature? ⟨1516⟩ = some ⟨[], []⟩ :=
  ⟨originalThreadSetupFunction, threadSetupSignature⟩

example {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {functionAddress memoryAddress : Nat} {fi : FuncInst H}
    {mem : MemInst} (slot : caller.module.funcs[1516]? = some functionAddress)
    (entry : s.funcs[functionAddress]? = some fi) (code : fi.code = .wasm threadSetupFunction)
    (signature : Expand fi.type (.func .nil .nil))
    (mapped : s.mem? (Frame.forCall fi.module [] threadSetupFunction.locals) ⟨0⟩ =
      some (memoryAddress, mem))
    (bound : 59984 ≤ mem.bytes.size) :
    ∃ word : BitVec 32, Memory.load mem.bytes 59892 4 = some word ∧
      Steps P host ⟨s, caller, [.plain (.call ⟨1516⟩)]⟩
        ⟨s.setMem memoryAddress (threadSetupMemory mem word), caller, []⟩ :=
  threadSetupReturns slot entry code signature mapped bound

#print axioms originalThreadSetupFunction
#print axioms threadSetupSignature
#print axioms threadSetupReturns
