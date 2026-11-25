module

public import SqliteWasm.DirectPreparation
public import SqliteWasm.GetVarint
import SqliteWasm.PutVarintTwoByte
import Silmaril.Formats.Sqlite.Varint.Thms
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 65536

private def writer : Func := (definedFunction? sqlite 530).get (by kernel_rfl)
private def writerType : DefType := ((allocTypes sqlite.types)[writer.type.toNat]?).get (by kernel_rfl)
private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)
private def readerType : DefType := ((allocTypes sqlite.types)[reader.type.toNat]?).get (by kernel_rfl)

private theorem viewOfWrittenByte {initial after : ByteArray}
    {payload : Silmaril.Formats.Bytes} {address index : Nat}
    (write : Memory.writeBytes initial address payload.data = some after)
    (inside : index < payload.length) :
    (File.View.ofBytes ⟨after⟩).get? (address + index) = payload.toList[index]? := by
  have insideBytes : index < payload.data.size := inside
  have fits := (Memory.writeBytes_eq_some_iff initial payload.data after address).mp write |>.1
  have sameSize := Memory.writeBytes_size initial payload.data after address write
  have readBack := Memory.readBytes_writeBytes initial payload.data after address write
  have extract := (Memory.readBytes_eq_some_iff after payload.data address payload.data.size).mp readBack |>.2
  have position : address + index < after.size := by omega
  have payloadIndex : index < (after.extract address (address + payload.data.size)).size := by
    rwa [← extract]
  have value : after[address + index] = payload.data[index] := by
    rw [← ByteArray.getElem_extract payloadIndex]
    simp only [← extract]
  rw [Silmaril.Formats.Bytes.toList, Array.getElem?_toList,
    getElem?_pos payload.data.data index (show index < payload.data.data.size from insideBytes)]
  simpa [File.View.get?, File.View.ofBytes, Silmaril.Formats.Bytes.length, position,
    ByteArray.getElem_eq_getElem_data] using value

/-- On the directly prepared reactor, the internal two-byte writer and reader
return their widths and leave the exact two writes in the same callee memory. -/
theorem reactorPreparedTwoByteRoundtrip (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧ mem.bytes.size = 131072 ∧
      ∀ (ptr : BitVec 32) (value : UInt64),
        128 ≤ value.toNat → value.toNat < 16384 → ptr.toNat + 8 ≤ mem.bytes.size →
        let written := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
        let final := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat = some (value, ptr.toNat + 2) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame, vals [.i32 2, .i32 2]⟩ := by
  obtain ⟨before, allocated, runtime, frame, mem, prepared, alloc, sameFunctions, _, _, mapped, size, _, _⟩ :=
    reactorDirectPreparation
  have writerBindings := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 507) (fn := writer) (d := writerType) alloc (by kernel_rfl) (by kernel_rfl)
  have readerBindings := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 411) (fn := reader) (d := readerType) alloc (by kernel_rfl) (by kernel_rfl)
  have writerSlot : frame.module.funcs[530]? = some (before.funcs.length + 507) := by
    simpa only [List.length_range] using writerBindings.1
  have readerSlot : frame.module.funcs[434]? = some (before.funcs.length + 411) := by
    simpa only [List.length_range] using readerBindings.1
  have writerEntry : runtime.funcs[before.funcs.length + 507]? = some ⟨writerType, frame.module, .wasm writer⟩ :=
    sameFunctions.symm ▸ writerBindings.2
  have writerSignature : Expand writerType (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  have readerSignature : Expand readerType (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  refine ⟨runtime, frame, mem, before.mems.length, prepared, mapped, size, ?_⟩
  intro ptr value lower upper bound
  dsimp only
  have fits : ptr.toNat + 2 ≤ mem.bytes.size := by omega
  let written := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
  let intermediate := runtime.setMem before.mems.length { mem with bytes := written }
  have put := putVarint_twoByte (P := P) (host := host) (ptr := ptr)
    (show definedFunction? sqlite 530 = some writer by kernel_rfl)
    writerSlot writerEntry rfl writerSignature lower upper mapped fits
  have readerEntry : intermediate.funcs[before.funcs.length + 411]? =
      some ⟨readerType, frame.module, .wasm reader⟩ := by
    change runtime.funcs[before.funcs.length + 411]? = _
    rw [sameFunctions]
    exact readerBindings.2
  have writtenMemory : intermediate.mem? { module := frame.module } ⟨0⟩ =
      some (before.mems.length, { mem with bytes := written }) := by
    unfold Store.mem? at mapped
    obtain ⟨a, slot, rest⟩ := Option.bind_eq_some_iff.mp mapped
    obtain ⟨m, entry, pair⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj pair)
    have index := (List.getElem?_eq_some_iff.mp entry).1
    simp [Store.mem?, intermediate, Store.setMem, slot, List.getElem?_set_self index]
  have writeWidth : (Varint.encode value).length = 2 := by simp [encode_two value lower upper]
  have wrote : Memory.writeBytes mem.bytes ptr.toNat (Varint.encode value).data = some written := by
    unfold Memory.writeBytes
    change (if ptr.toNat + (Varint.encode value).length ≤ mem.bytes.size then
      some written else none) = some written
    rw [writeWidth, ite_eq_left fits]
  have writtenSize := Memory.writeBytes_size _ _ _ _ wrote
  have readFits : ptr.toNat + 8 ≤ written.size := by omega
  have read : Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat =
      some (value, ptr.toNat + 2) := by
    apply Varint.read?_encode_two _ _ _ lower upper
    intro index inside
    exact viewOfWrittenByte wrote (by rwa [writeWidth])
  refine ⟨read, ?_⟩
  have get := getVarint_of_read (P := P) (host := host) (src := ptr) (dst := ptr)
    (show definedFunction? sqlite 434 = some reader by kernel_rfl)
    readerSlot readerEntry rfl readerSignature writtenMemory read readFits
  rw [writeWidth] at put
  have readWidth : ptr.toNat + 2 - ptr.toNat = 2 := by omega
  rw [readWidth] at get
  have finalStore :
      intermediate.setMem before.mems.length
        { mem with bytes := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat) } =
      runtime.setMem before.mems.length
        { mem with bytes := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat) } := by
    simp [intermediate, Store.setMem, List.set_set]
  rw [finalStore] at get
  have putInContext := Steps.ctxtInstrs (vs := [])
    (rest := vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]) put
  have getInContext := Steps.ctxtInstrs (vs := [.i32 2]) (rest := []) get
  exact putInContext.trans getInContext

#print axioms reactorPreparedTwoByteRoundtrip

end SqliteWasm
