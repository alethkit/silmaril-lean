module

public import SqliteWasm.DirectPreparation
public import SqliteWasm.GetVarint
import SqliteWasm.OrdinaryVarintHelper
import Silmaril.Formats.Sqlite.Varint.Normal.Thms
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact
open ThreeByte (callFrame)
open ThreeByte.Symbolic (quotedHelper)

set_option maxRecDepth 65536

private def writer : Func := (definedFunction? sqlite 530).get (by kernel_rfl)
private def writerType : DefType := ((allocTypes sqlite.types)[writer.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType :=
  ((allocTypes sqlite.types)[quotedHelper.type.toNat]?).get (by kernel_rfl)
private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)
private def readerType : DefType := ((allocTypes sqlite.types)[reader.type.toNat]?).get (by kernel_rfl)

private def stackGlobal : Global := (sqlite.globals[0]?).get rfl

private theorem stackGlobalLookup {before allocated runtime : Store Nat} {frame : Frame}
    (alloc : allocModule? before sqlite reactorImportAddrs [.i32 126112, .i32 0]
      [.null] [reactorElementRefs] = some (allocated, frame.module))
    (sameGlobals : runtime.globals = allocated.globals) :
    runtime.global? frame ⟨0⟩ = some (before.globals.length, ⟨⟨.var, .i32⟩, .i32 126112⟩) := by
  have binding := Link.GC.Preparation.allocModule_global (as := List.range 23)
    (n := 0) (g := stackGlobal) (v := .i32 126112) alloc (by rfl) (by rfl)
  have slot : frame.module.globals[0]? = some before.globals.length := binding.1
  have entry : allocated.globals[before.globals.length]? =
      some ⟨⟨.var, .i32⟩, .i32 126112⟩ := binding.2
  change (frame.module.globals[0]?.bind fun address =>
    runtime.globals[address]?.bind fun g => some (address, g)) = _
  rw [slot, Option.bind_some, sameGlobals, entry]
  rfl

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

/-- The prepared reactor's writer and reader compose the scratch, encoding, and
little-endian output splices in execution order. Readback may overlap scratch. -/
theorem reactorPreparedOrdinaryRoundtrip (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧ mem.bytes.size = 131072 ∧
      ∀ (ptr : BitVec 32) (value : UInt64) (width : Nat),
        3 ≤ width → width ≤ 8 →
        128 ^ (width - 1) ≤ value.toNat → value.toNat < 128 ^ width →
        ptr.toNat + 8 ≤ mem.bytes.size →
        (ptr.toNat + width ≤ 126102 ∨ 126102 + width ≤ ptr.toNat) →
        let scratch := Memory.writeSlice mem.bytes 126102 ⟨⟨(Varint.encode value).toList.reverse⟩⟩
        let written := Memory.writeSlice scratch ptr.toNat (Varint.encode value).data
        let final := Memory.writeSlice written ptr.toNat (Memory.encodeLE 8 value.toNat)
        Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat = some (value, ptr.toNat + width) ∧
        Steps P host
          ⟨runtime, frame, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)] ++
            vals [.i32 ptr, .i32 ptr] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem address { mem with bytes := final }, frame, vals [.i32 (BitVec.ofNat 32 width), .i32 (BitVec.ofNat 32 width)]⟩ := by
  obtain ⟨before, allocated, runtime, frame, mem, prepared, alloc, sameFunctions,
    _, _, mapped, size, _, _, sameGlobals⟩ := reactorDirectPreparationWithGlobals
  have stack := stackGlobalLookup alloc sameGlobals
  have writerBindings := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 507) (fn := writer) (d := writerType) alloc (by kernel_rfl) (by kernel_rfl)
  have helperBindings := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 524) (fn := quotedHelper) (d := helperType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have readerBindings := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 411) (fn := reader) (d := readerType) alloc (by kernel_rfl) (by kernel_rfl)
  have writerSlot : frame.module.funcs[530]? = some (before.funcs.length + 507) := by
    simpa only [List.length_range] using writerBindings.1
  have helperSlot : frame.module.funcs[547]? = some (before.funcs.length + 524) := by
    simpa only [List.length_range] using helperBindings.1
  have readerSlot : frame.module.funcs[434]? = some (before.funcs.length + 411) := by
    simpa only [List.length_range] using readerBindings.1
  have writerEntry : runtime.funcs[before.funcs.length + 507]? = some ⟨writerType, frame.module, .wasm writer⟩ :=
    sameFunctions.symm ▸ writerBindings.2
  have helperEntry : runtime.funcs[before.funcs.length + 524]? =
      some ⟨helperType, frame.module, .wasm quotedHelper⟩ :=
    sameFunctions.symm ▸ helperBindings.2
  have writerSignature : Expand writerType (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  have helperSignature : Expand helperType (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  have readerSignature : Expand readerType (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  refine ⟨runtime, frame, mem, before.mems.length, prepared, mapped, size, ?_⟩
  intro ptr value width entered normal lower upper fits disjoint
  dsimp only
  have exactWidth : OrdinaryVarint.Width value.toNat width := ⟨by omega, normal, lower, upper⟩
  let scratch := Memory.writeSlice mem.bytes 126102 (ThreeByte.scratchBytes value)
  let written := Memory.writeSlice scratch ptr.toNat (Varint.encode value).data
  let intermediate := runtime.setMem before.mems.length { mem with bytes := written }
  have putBinding : runtime.func? frame ⟨530⟩ =
      some (before.funcs.length + 507, ⟨writerType, frame.module, .wasm writer⟩) := by
    unfold Store.func?
    change (frame.module.funcs[530]?.bind fun address =>
      runtime.funcs[address]?.bind fun fn => some (address, fn)) = _
    rw [writerSlot, Option.bind_some, writerEntry]
    rfl
  have helperBinding : runtime.func? (callFrame frame.module writer ptr value) ⟨547⟩ =
      some (before.funcs.length + 524, ⟨helperType, frame.module, .wasm quotedHelper⟩) := by
    unfold Store.func?
    change (frame.module.funcs[547]?.bind fun address =>
      runtime.funcs[address]?.bind fun fn => some (address, fn)) = _
    rw [helperSlot, Option.bind_some, helperEntry]
    rfl
  have writerBounds : OrdinaryVarint.Buffers mem.bytes ptr 126112 width := by
    refine ⟨by decide, by omega, by omega, ?_, disjoint⟩
    change 126102 + width ≤ mem.bytes.size
    omega
  have put := OrdinaryVarint.putVarint_ordinary (P := P) (host := host) (ptr := ptr)
    (show definedFunction? sqlite 530 = some writer by kernel_rfl)
    putBinding helperBinding rfl rfl writerSignature helperSignature entered exactWidth mapped stack writerBounds
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
  have writeWidth : (Varint.encode value).length = width :=
    OrdinaryVarint.ordinaryLength value width exactWidth
  have scratchFits : 126102 + (ThreeByte.scratchBytes value).size ≤ mem.bytes.size := by
    rw [OrdinaryVarint.scratchLength value width exactWidth]
    omega
  have scratchWrite : Memory.writeBytes mem.bytes 126102 (ThreeByte.scratchBytes value) = some scratch := by
    rw [Memory.writeBytes, ite_eq_left scratchFits]
  have scratchSize := Memory.writeBytes_size _ _ _ _ scratchWrite
  have outputFits : ptr.toNat + width ≤ scratch.size := by omega
  have wrote : Memory.writeBytes scratch ptr.toNat (Varint.encode value).data = some written := by
    unfold Memory.writeBytes
    change (if ptr.toNat + (Varint.encode value).length ≤ scratch.size then
      some written else none) = some written
    rw [writeWidth, ite_eq_left outputFits]
  have writtenSize := Memory.writeBytes_size _ _ _ _ wrote
  have readFits : ptr.toNat + 8 ≤ written.size := by omega
  have read : Varint.read? (File.View.ofBytes ⟨written⟩) ptr.toNat =
      some (value, ptr.toNat + width) := by
    apply Varint.read?_encode_normal _ _ _ _ exactWidth.positive normal (Or.inr lower) upper
    intro index inside
    exact viewOfWrittenByte wrote (by rwa [writeWidth])
  refine ⟨read, ?_⟩
  have get := getVarint_of_read (P := P) (host := host) (src := ptr) (dst := ptr)
    (show definedFunction? sqlite 434 = some reader by kernel_rfl)
    readerSlot readerEntry rfl readerSignature writtenMemory read readFits
  have readWidth : ptr.toNat + width - ptr.toNat = width := by omega
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
  have getInContext := Steps.ctxtInstrs (vs := [.i32 (BitVec.ofNat 32 width)]) (rest := []) get
  exact putInContext.trans getInContext

#print axioms reactorPreparedOrdinaryRoundtrip

end SqliteWasm
