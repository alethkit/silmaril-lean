module

public import SqliteWasm.PreparedInvocation
public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
import SqliteWasm.GetVarintOneByte
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Logic.Memory.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (bytesAt getElem?_bytesAt leNat leNat_cons leNat_lt length_bytesAt load_eq)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private theorem updatedMemory {s : Store Nat} {frame : Frame} {address : Nat}
    {mem : MemInst} (found : s.mem? frame ⟨0⟩ = some (address, mem)) (after : MemInst) :
    (s.setMem address after).mem? frame ⟨0⟩ = some (address, after) := by
  change (frame.module.mems[0]?.bind fun a => s.mems[a]?.bind fun m => some (a, m)) = _ at found
  obtain ⟨a, slot, lookup⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨m, entry, same⟩ := Option.bind_eq_some_iff.mp lookup
  obtain ⟨sameAddress, sameMemory⟩ := Prod.mk.inj (Option.some.inj same)
  subst a
  subst m
  change (frame.module.mems[0]?.bind fun a =>
    (s.mems.set address after)[a]?.bind fun m => some (a, m)) = _
  rw [slot, Option.bind_some, List.getElem?_set_self (List.getElem?_eq_some_iff.mp entry).1]
  rfl

private theorem storeWordSize (bytes : ByteArray) (offset : Nat) (word : Nat)
    (fits : offset + 4 ≤ bytes.size) :
    (Memory.writeSlice bytes offset (Memory.encodeLE 4 word)).size = bytes.size :=
  Memory.writeBytes_size bytes (Memory.encodeLE 4 word) _ offset (by
    simp only [Memory.writeBytes, Memory.encodeLE_size, ite_eq_left fits])

private theorem setupWritesSize (writes : List (Nat × BitVec 32)) (mem : MemInst)
    (fits : ∀ w ∈ writes, w.1 + 4 ≤ mem.bytes.size) :
    (writes.foldl (fun current (offset, word) =>
      { current with bytes := Memory.writeSlice current.bytes offset (Memory.encodeLE 4 word.toNat) })
      mem).bytes.size = mem.bytes.size := by
  induction writes generalizing mem with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨offset, word⟩ := head
    let next := { mem with bytes := Memory.writeSlice mem.bytes offset (Memory.encodeLE 4 word.toNat) }
    have size := storeWordSize mem.bytes offset word.toNat (fits (offset, word) List.mem_cons_self)
    rw [List.foldl_cons]
    exact (ih next (fun w hw => size.symm ▸ fits w (List.mem_cons_of_mem _ hw))).trans size

private theorem initializedSize (mem : MemInst) (fits : 59984 ≤ mem.bytes.size) :
    (threadSetupMemory (initializerMark mem 0) 0).bytes.size = mem.bytes.size := by
  have markedSize : (initializerMark mem 0).bytes.size = mem.bytes.size :=
    storeWordSize _ 59328 1 (by omega)
  unfold threadSetupMemory
  rw [setupWritesSize, markedSize]
  intro w membership
  rw [markedSize]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem markerByte {B : ByteArray} (fits : 59332 ≤ B.size)
    (loaded : Memory.load B 59328 4 = some 1) : B[59328]? = some 1 := by
  have length : (bytesAt B ⟨59328, 4⟩).length = 4 := length_bytesAt fits
  have wordFits := leNat_lt (bytesAt B ⟨59328, 4⟩)
  rw [length] at wordFits
  have word := load_eq (B := B) (a := 59328) (n := 4) fits
  rw [loaded] at word
  have value := congrArg BitVec.toNat (Option.some.inj word.symm)
  change (BitVec.ofNat (8 * 4) (leNat (bytesAt B ⟨59328, 4⟩))).toNat = 1 at value
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordFits] at value
  cases bytes : bytesAt B ⟨59328, 4⟩ with
  | nil => simp [bytes] at length
  | cons first rest =>
    rw [bytes, leNat_cons] at value
    have one : first = 1 := UInt8.toNat.inj (by change first.toNat = 1; omega)
    have get := getElem?_bytesAt B ⟨59328, 4⟩ 0
    rw [bytes, one] at get
    have read : B.data[59328]? = some 1 := by simpa using get.symm
    have index : 59328 < B.size := by omega
    simpa [getElem?_pos B 59328 index, ByteArray.getElem_eq_getElem_data,
      getElem?_pos B.data 59328 (show 59328 < B.data.size from index)] using read

private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)
private def readerType : DefType := ((allocTypes sqlite.types)[reader.type.toNat]?).get (by kernel_rfl)

/-- The prepared initializer marks a byte that the pinned slot-434 reader
consumes as the one-byte varint 1. The destination may overlap the source. -/
theorem reactorPostInitVarint (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress readerAddress fn fi,
      let after := threadSetupMemory (initializerMark mem 0) 0
      let initialized := runtime.setMem memoryAddress after
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func 25⟩ ∧
      InvokeOk runtime 25 [] ∧
      Steps P host (invoke runtime 25 []) ⟨initialized, {}, []⟩ ∧
      definedFunction? sqlite 434 = some fn ∧
      frame.module.funcs[434]? = some readerAddress ∧
      runtime.funcs[readerAddress]? = some fi ∧
      initialized.funcs[readerAddress]? = some fi ∧
      fi.code = .wasm fn ∧
      initialized.mem? { module := fi.module } ⟨0⟩ = some (memoryAddress, after) ∧
      after.bytes.size = 131072 ∧
      Varint.read? (File.View.ofBytes ⟨after.bytes⟩) 59328 = some (1, 59329) ∧
      ∀ dst : BitVec 32, dst.toNat + 8 ≤ after.bytes.size →
        Steps P host ⟨initialized, frame, vals [.i32 59328, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨initialized.setMem memoryAddress
            { after with bytes := Memory.writeSlice after.bytes dst.toNat (Memory.encodeLE 8 1) },
            frame, [constI32 1]⟩ := by
  obtain ⟨runtime, frame, mem, memoryAddress, prepared, exported, mapped, initOk, runInit⟩ :=
    reactorPreparedInvocation P host
  obtain ⟨before, allocated, directStore, directFrame, directMem, prepared', alloc, sameFunctions,
    _, _, mapped', size, _, _⟩ := reactorDirectPreparation
  obtain ⟨sameStore, frameAndStart⟩ := Prod.mk.inj (Option.some.inj (prepared.symm.trans prepared'))
  have sameFrame := (Prod.mk.inj frameAndStart).1
  subst directStore
  subst directFrame
  have sameMem := (Prod.mk.inj (Option.some.inj (mapped.symm.trans mapped'))).2
  subst directMem
  let after := threadSetupMemory (initializerMark mem 0) 0
  let initialized := runtime.setMem memoryAddress after
  let readerAddress := before.funcs.length + 411
  let fi : FuncInst Nat := ⟨readerType, frame.module, .wasm reader⟩
  have binding := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 411) (fn := reader) (d := readerType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have selected : definedFunction? sqlite 434 = some reader := by kernel_rfl
  have slot : frame.module.funcs[434]? = some readerAddress := by
    simpa only [List.length_range] using binding.1
  have entry : runtime.funcs[readerAddress]? = some fi := sameFunctions.symm ▸ binding.2
  have retained : initialized.funcs[readerAddress]? = some fi := entry
  have signature : Expand readerType (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  have postMapped : initialized.mem? { module := fi.module } ⟨0⟩ = some (memoryAddress, after) :=
    updatedMemory mapped after
  have fits : 59984 ≤ mem.bytes.size := by omega
  have afterSize : after.bytes.size = 131072 := (initializedSize mem fits).trans size
  have marked := initializerFlagStaysMarked mem 0 fits
  have low : after.bytes[59328]? = some 1 := markerByte (by omega) marked
  have read dst bound :=
    getVarint_oneByte (P := P) (host := host) (src := 59328) (dst := dst)
      selected slot retained rfl signature postMapped low (by decide) bound
  have overlapFits : (59328#32).toNat + 8 ≤ after.bytes.size := by
    change 59336 ≤ after.bytes.size
    omega
  exact ⟨runtime, frame, mem, memoryAddress, readerAddress, reader, fi, prepared, exported, initOk,
    runInit, selected, slot, entry, retained, rfl, postMapped, afterSize,
    (read 59328 overlapFits).1, fun dst bound => (read dst bound).2⟩

#print axioms reactorPostInitVarint

end SqliteWasm
