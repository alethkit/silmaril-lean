module

public import SqliteWasm.DirectPreparation
public import SqliteWasm.GetVarint
import SqliteWasm.PutVarintCheck
import SqliteWasm.GetVarintReaderSupport
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

private theorem readWrittenByte {bytes : ByteArray} {address : Nat} {value : UInt64}
    (small : value.toNat < 128) (bound : address + 1 ≤ bytes.size) :
    let after := Memory.writeSlice bytes address (Varint.encode value).data
    after.size = bytes.size ∧
      Varint.read? (File.View.ofBytes ⟨after⟩) address = some (value, address + 1) := by
  let octet := UInt8.ofNat value.toNat
  let encoded : ByteArray := ⟨#[octet]⟩
  have encoding : (Varint.encode value).data = encoded := by
    rw [encode_one_byte value small]
    rfl
  rw [encoding]
  let after := Memory.writeSlice bytes address encoded
  have encodedSize : encoded.size = 1 := rfl
  have wrote : Memory.writeBytes bytes address encoded = some after := by
    rw [Memory.writeBytes, encodedSize, ite_eq_left bound]
  have sameSize := Memory.writeBytes_size bytes encoded after address wrote
  refine ⟨sameSize, ?_⟩
  have octetValue : octet.toNat = value.toNat := by
    simp [octet, Nat.mod_eq_of_lt (show value.toNat < 256 by omega)]
  obtain ⟨_, splice⟩ := (Memory.writeBytes_eq_some_iff bytes encoded after address).mp wrote
  have prefixSize : (bytes.extract 0 address).size = address := by
    simp only [ByteArray.size_extract]
    omega
  have prefixBound : address < (bytes.extract 0 address ++ encoded).size := by
    simp [prefixSize, encodedSize]
  have loaded : after[address]? = some octet := by
    rw [getElem?_pos after address (by omega)]
    simp only [splice, ByteArray.getElem_append_left prefixBound,
      ByteArray.getElem_append_right (Nat.le_of_eq prefixSize), prefixSize, Nat.sub_self]
    rfl
  have fetched := GetVarintReaderSupport.viewByte after address octet loaded
  change Varint.read? (File.View.ofBytes ⟨after⟩) address = _
  simp [-Memory.writeSlice_eq, Varint.read?, Varint.readNat?, Varint.readAux?, fetched,
    octetValue, small, Nat.mod_eq_of_lt small]

/-- On the directly prepared reactor, the internal one-byte writer and reader
return their widths and leave the exact two writes in the same callee memory. -/
theorem reactorPreparedOneByteRoundtrip (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧ mem.bytes.size = 131072 ∧
      ∀ (ptr : BitVec 32) (value : UInt64), value.toNat < 128 → ptr.toNat + 8 ≤ mem.bytes.size →
        let written := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
        let final := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat = some (value, ptr.toNat + 1) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame, vals [.i32 1, .i32 1]⟩ := by
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
  intro ptr value small bound
  dsimp only
  have fits : ptr.toNat + 1 ≤ mem.bytes.size := by omega
  let written := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
  let intermediate := runtime.setMem before.mems.length { mem with bytes := written }
  have put := putVarint_oneByte (P := P) (host := host) (ptr := ptr)
    (show definedFunction? sqlite 530 = some writer by kernel_rfl)
    writerSlot writerEntry rfl writerSignature small mapped fits
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
  obtain ⟨writtenSize, read⟩ := readWrittenByte (value := value) small fits
  have readFits : ptr.toNat + 8 ≤ written.size := by
    change written.size = mem.bytes.size at writtenSize
    omega
  refine ⟨read, ?_⟩
  have get := getVarint_of_read (P := P) (host := host) (src := ptr) (dst := ptr)
    (show definedFunction? sqlite 434 = some reader by kernel_rfl)
    readerSlot readerEntry rfl readerSignature writtenMemory read readFits
  have writeWidth : (Varint.encode value).length = 1 := by simp [encode_one_byte value small]
  rw [writeWidth] at put
  have readWidth : ptr.toNat + 1 - ptr.toNat = 1 := by omega
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
  have getInContext := Steps.ctxtInstrs (vs := [.i32 1]) (rest := []) get
  exact putInContext.trans getInContext

#print axioms reactorPreparedOneByteRoundtrip

end SqliteWasm
