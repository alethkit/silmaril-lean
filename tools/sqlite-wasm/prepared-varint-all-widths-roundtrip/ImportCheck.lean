module

import SqliteWasm.PreparedVarintAllWidths

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 131072

private def boundaries : List UInt64 :=
  [0, 127, 128, 16383, 16384, 0x00ffffffffffffff, 0x0100000000000000, 0xffffffffffffffff]

private def reaches (P : Profile) (host : HostSemantics Nat) (runtime : Store Nat)
    (frame : Frame) (mem : MemInst) (address : Nat) (ptr : BitVec 32) (value : UInt64) : Prop :=
  let width := (Varint.encode value).length
  let scratch := if 16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56 then
    Memory.writeSlice mem.bytes 126102 ⟨⟨(Varint.encode value).toList.reverse⟩⟩
    else mem.bytes
  let written := Memory.writeSlice scratch ptr.toNat (Varint.encode value).data
  let final := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat)
  Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat = some (value, ptr.toNat + width) ∧
  Steps P host
    ⟨runtime, frame, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
      vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩
    ⟨runtime.setMem address { mem with bytes := final }, frame,
      vals [.i32 (BitVec.ofNat 32 width), .i32 (BitVec.ofNat 32 width)]⟩

example (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      ((Binary.Core.decode? originalBytes.toByteArray).bind
        (fun decoded => prepareDirect? evalConst? reactorTypedImports decoded reactorImportAddrs)) =
          some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      (∀ value ∈ boundaries, reaches P host runtime frame mem address 131063 value) ∧
      reaches P host runtime frame mem address 126098 16384 := by
  rw [originalDecode, Option.bind_some]
  obtain ⟨runtime, frame, mem, address, prepared, mapped, size, call⟩ :=
    reactorPreparedVarintRoundtrip P host
  refine ⟨runtime, frame, mem, address, prepared, mapped, ?_, ?_⟩
  · intro value member
    have width : (Varint.encode value).length ≤ 9 := by
      simp only [boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide +kernel
    have maxWidth : max 8 (Varint.encode value).length ≤ 9 := max_le (by decide) width
    apply call 131063 value
    · change 131063 + max 8 (Varint.encode value).length ≤ mem.bytes.size
      omega
    · intro _ _
      right
      change 126102 + (Varint.encode value).length ≤ 131063
      omega
  · exact call 126098 16384 (by rw [size]; decide +kernel)
      (fun _ _ => by decide +kernel)

-- At the last eight-byte start, a nine-byte encoding exceeds the bound.
example :
    131072 < (131064 : BitVec 32).toNat +
      max 8 (Varint.encode (0x0100000000000000 : UInt64)).length := by
  decide +kernel

#print axioms originalDecode
#print axioms reactorPreparedVarintRoundtrip

end SqliteWasm
