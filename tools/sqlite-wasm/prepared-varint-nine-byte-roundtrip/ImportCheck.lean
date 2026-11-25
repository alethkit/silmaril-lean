module

import SqliteWasm.PreparedVarintNineByteRoundtrip
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

-- Both endpoints at the last address that fits the nine-byte output.
example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      ∀ (value : UInt64), value = 0x0100000000000000 ∨ value = 0xffffffffffffffff →
        let written := Memory.writeSlice mem.bytes 131063 (Varint.encode value).data
        let final := Memory.writeSlice written 131063 (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) 131063 = some (value, 131072) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 131063, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 131063, .i32 131063] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame, vals [.i32 9, .i32 9]⟩ := by
  rw [originalDecode, Option.bind_some]
  obtain ⟨runtime, frame, mem, address, prep, mapped, size, roundtrip⟩ :=
    reactorPreparedNineByteRoundtrip P host
  refine ⟨runtime, frame, mem, address, prep, mapped, ?_⟩
  intro value endpoint
  have fits : (131063 : BitVec 32).toNat + 9 ≤ mem.bytes.size := by
    rw [size]
    decide +kernel
  rcases endpoint with rfl | rfl
  · exact roundtrip 131063 0x0100000000000000 (by decide +kernel) fits
  · exact roundtrip 131063 0xffffffffffffffff (by decide +kernel) fits

private def writer : Func := (definedFunction? sqlite 530).get (by kernel_rfl)
private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 547).get (by kernel_rfl)
private def typeFor (fn : Func) : Option DefType := (allocTypes sqlite.types)[fn.type.toNat]?

private def caller : Frame :=
  { module := { funcs := (List.replicate 434 0) ++ [1] ++ (List.replicate 112 0) ++ [2], mems := [0], globals := [0] }
    locals := [some (.i32 42)] }

private def memory : MemInst :=
  ⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[0xa5, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0x5a]⟩⟩

private def initial : Store Nat :=
  { funcs := [⟨(typeFor writer).get (by kernel_rfl), caller.module, .wasm writer⟩,
              ⟨(typeFor reader).get (by kernel_rfl), caller.module, .wasm reader⟩,
              ⟨(typeFor helper).get (by kernel_rfl), caller.module, .wasm helper⟩]
    mems := [memory]
    globals := [⟨⟨.var, .i32⟩, .i32 126112⟩] }

private def replayWriter (value : BitVec 64) (expected : ByteArray) : Prop :=
  runIK neverFail 512
    ⟨initial, caller, vals [.i32 1, .i64 value] ++ [.plain (.call ⟨530⟩)]⟩ =
    (⟨initial.setMem 0 { memory with bytes := expected }, caller, [constI32 9]⟩, true)

private def replay (value : BitVec 64) (expected : ByteArray) : Prop :=
  runIK neverFail 512
    ⟨initial, caller, vals [.i32 1, .i64 value] ++ [.plain (.call ⟨530⟩)] ++
      vals [.i32 1, .i32 1] ++ [.plain (.call ⟨434⟩)]⟩ =
    (⟨initial.setMem 0 { memory with bytes := expected }, caller, vals [.i32 9, .i32 9]⟩, true)

example : replayWriter 0x0100000000000000
    ⟨#[0xa5, 0x80, 0xc0, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0, 0x5a]⟩ := by
  unfold replayWriter
  kernel_rfl

example : replayWriter 0xffffffffffffffff
    ⟨#[0xa5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x5a]⟩ := by
  unfold replayWriter
  kernel_rfl

example : replay 0x0100000000000000 ⟨#[0xa5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0x5a]⟩ := by
  unfold replay
  kernel_rfl

example : replay 0x0100000000000012 ⟨#[0xa5, 0x12, 0, 0, 0, 0, 0, 0, 1, 0x12, 0x5a]⟩ := by
  unfold replay
  kernel_rfl

example : replay 0xffffffffffffffff ⟨#[0xa5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x5a]⟩ := by
  unfold replay
  kernel_rfl

#print axioms originalDecode
#print axioms originalPutVarintFunction
#print axioms originalGetVarintFunction
#print axioms originalPutVarintLongFunction
#print axioms reactorPreparedNineByteRoundtrip

end SqliteWasm
