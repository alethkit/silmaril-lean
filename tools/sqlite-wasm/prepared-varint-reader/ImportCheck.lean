module

import SqliteWasm.PreparedVarintReader

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open SqliteWasm

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (memoryAddress, mem) ∧
      ∀ {src dst : BitVec 32} {value : UInt64} {next : Nat},
        Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat = some (value, next) →
        dst.toNat + 8 ≤ mem.bytes.size →
        Steps P host ⟨runtime, frame, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem memoryAddress
            { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 value.toNat) },
            frame, [constI32 (BitVec.ofNat 32 (next - src.toNat))]⟩ := by
  rw [originalDecode, Option.bind_some]
  exact reactorPreparedReader P host

#print axioms originalDecode
#print axioms reactorPreparedReader
