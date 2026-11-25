module

import SqliteWasm.PreparedVarintTwoByteRoundtrip
import Silmaril.Wasm.Verify.Kernel.Defs

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType)
open Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 1000000

-- Both endpoints at the last address that fits the full readback.
example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      ∀ (value : UInt64), value = 128 ∨ value = 16383 →
        let written := Memory.writeSlice mem.bytes 131064 (Varint.encode value).data
        let final := Memory.writeSlice written 131064 (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) 131064 = some (value, 131066) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 131064, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 131064, .i32 131064] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame, vals [.i32 2, .i32 2]⟩ := by
  rw [originalDecode, Option.bind_some]
  obtain ⟨runtime, frame, mem, address, prep, mapped, size, roundtrip⟩ :=
    reactorPreparedTwoByteRoundtrip P host
  refine ⟨runtime, frame, mem, address, prep, mapped, ?_⟩
  intro value endpoint
  have fits : (131064 : BitVec 32).toNat + 8 ≤ mem.bytes.size := by
    rw [size]
    decide +kernel
  rcases endpoint with rfl | rfl
  · exact roundtrip 131064 128 (by decide +kernel) (by decide +kernel) fits
  · exact roundtrip 131064 16383 (by decide +kernel) (by decide +kernel) fits

private def writer : Func := (definedFunction? sqlite 530).get (by kernel_rfl)
private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)
private def typeFor (fn : Func) : Option DefType := (allocTypes sqlite.types)[fn.type.toNat]?

private def caller : Frame :=
  { module := { funcs := (List.replicate 434 0) ++ [1] ++ (List.replicate 96 0), mems := [0] }
    locals := [some (.i32 42)] }

private def memory : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0x5a]⟩⟩

private def initial : Store Nat :=
  { funcs := [⟨(typeFor writer).get (by kernel_rfl), caller.module, .wasm writer⟩,
              ⟨(typeFor reader).get (by kernel_rfl), caller.module, .wasm reader⟩]
    mems := [memory] }

private def replayWriter (value : BitVec 64) (first second : UInt8) : Prop :=
  runIK neverFail 64
    ⟨initial, caller, vals [.i32 1, .i64 value] ++ [.plain (.call ⟨530⟩)]⟩ =
    (⟨initial.setMem 0
        { memory with bytes := ⟨#[0xa5, first, second, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0x5a]⟩ },
      caller, [constI32 2]⟩, true)

private def replay (value : BitVec 64) (low high : UInt8) : Prop :=
  runIK neverFail 192
    ⟨initial, caller, vals [.i32 1, .i64 value] ++ [.plain (.call ⟨530⟩)] ++
      vals [.i32 1, .i32 1] ++ [.plain (.call ⟨434⟩)]⟩ =
    (⟨initial.setMem 0 { memory with bytes := ⟨#[0xa5, low, high, 0, 0, 0, 0, 0, 0, 0x5a]⟩ },
      caller, vals [.i32 2, .i32 2]⟩, true)

-- Observe both the writer's two bytes and the reader's eight bytes.
example : replayWriter 128 0x81 0 := by unfold replayWriter; kernel_rfl
example : replayWriter 16383 0xff 0x7f := by unfold replayWriter; kernel_rfl
example : replay 128 0x80 0 := by unfold replay; kernel_rfl
example : replay 16383 0xff 0x3f := by unfold replay; kernel_rfl

#print axioms originalDecode
#print axioms originalPutVarintFunction
#print axioms originalGetVarintFunction
#print axioms reactorPreparedTwoByteRoundtrip

end SqliteWasm
