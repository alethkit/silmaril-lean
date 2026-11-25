module

import SqliteWasm.PreparedVarintRoundtrip
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

-- The largest one-byte value at the last address that fits the full readback.
example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      let written := Memory.writeSlice mem.bytes 131064 (Varint.encode 127).data
      let final := Memory.writeSlice written 131064 (Memory.encodeLE 8 127)
      Varint.read? (File.View.ofBytes ⟨written⟩) 131064 = some (127, 131065) ∧
      Steps P host
        ⟨runtime, frame, vals [.i32 131064, .i64 127] ++ [.plain (.call ⟨530⟩)] ++
          vals [.i32 131064, .i32 131064] ++ [.plain (.call ⟨434⟩)]⟩
        ⟨runtime.setMem address { mem with bytes := final }, frame, vals [.i32 1, .i32 1]⟩ := by
  rw [originalDecode, Option.bind_some]
  obtain ⟨runtime, frame, mem, address, prep, mapped, size, roundtrip⟩ :=
    reactorPreparedOneByteRoundtrip P host
  exact ⟨runtime, frame, mem, address, prep, mapped,
    roundtrip 131064 127 (by decide +kernel) (by rw [size]; decide +kernel)⟩

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

private def replay (value : BitVec 64) (octet : UInt8) : Prop :=
  runIK neverFail 128
    ⟨initial, caller, vals [.i32 1, .i64 value] ++ [.plain (.call ⟨530⟩)] ++
      vals [.i32 1, .i32 1] ++ [.plain (.call ⟨434⟩)]⟩ =
    (⟨initial.setMem 0 { memory with bytes := ⟨#[0xa5, octet, 0, 0, 0, 0, 0, 0, 0, 0x5a]⟩ },
      caller, vals [.i32 1, .i32 1]⟩, true)

-- Replay the writer alone to observe the intermediate one-byte update.
example :
    runIK neverFail 64
      ⟨initial, caller, vals [.i32 1, .i64 127] ++ [.plain (.call ⟨530⟩)]⟩ =
      (⟨initial.setMem 0
          { memory with bytes := ⟨#[0xa5, 127, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0xee, 0x5a]⟩ },
        caller, [constI32 1]⟩, true) := by
  kernel_rfl

-- Both calls leave the enclosing sentinels intact in the manually linked fixture.
example : replay 0 0 := by unfold replay; kernel_rfl
example : replay 127 127 := by unfold replay; kernel_rfl

#print axioms originalDecode
#print axioms originalPutVarintFunction
#print axioms originalGetVarintFunction
#print axioms reactorPreparedOneByteRoundtrip

end SqliteWasm
