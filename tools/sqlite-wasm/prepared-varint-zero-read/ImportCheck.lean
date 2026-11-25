module

import SqliteWasm.PreparedVarintZeroRead
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType)
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 1000000

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      Steps P host ⟨runtime, frame, vals [.i32 59328, .i32 59328] ++ [.plain (.call ⟨434⟩)]⟩
        ⟨runtime.setMem address
          { mem with bytes := Memory.writeSlice mem.bytes 59328 (Memory.encodeLE 8 0) },
          frame, [constI32 1]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedZeroRead P host

-- Replay the same fixed-address call in a directly linked zero-memory fixture.
private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)

private def runtimeType : DefType := ((allocTypes sqlite.types)[reader.type.toNat]?).get (by kernel_rfl)

private def caller : Frame :=
  { module := { funcs := List.range 435, mems := [0] }
    locals := [some (.i32 42)] }

private def memory : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨Array.replicate 59336 0⟩⟩

private def callee : FuncInst Nat := ⟨runtimeType, caller.module, .wasm reader⟩

private def initial : Store Nat :=
  { funcs := List.replicate 435 callee, mems := [memory] }

example :
    runIK neverFail 64
      ⟨initial, caller, vals [.i32 59328, .i32 59328] ++ [.plain (.call ⟨434⟩)]⟩ =
      (⟨initial.setMem 0
          { memory with bytes := Memory.writeSlice memory.bytes 59328 (Memory.encodeLE 8 0) },
        caller, [constI32 1]⟩, true) := by
  kernel_rfl

#print axioms originalDecode
#print axioms reactorPreparedZeroRead

end SqliteWasm
