module

public import SqliteWasm.PreparedVarintReader
import SqliteWasm.GetVarintReaderSupport
import Silmaril.Wasm.Logic.Memory.Thms

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Core (bytesAt getElem?_bytesAt leNat leNat_cons leNat_lt length_bytesAt load_eq)

set_option maxRecDepth 131072

private theorem firstByteOfZeroWord {B : ByteArray} {address : Nat}
    (fits : address + 4 ≤ B.size) (loaded : Memory.load B address 4 = some 0) :
    B[address]? = some 0 := by
  have length : (bytesAt B ⟨address, 4⟩).length = 4 := length_bytesAt fits
  have wordFits := leNat_lt (bytesAt B ⟨address, 4⟩)
  rw [length] at wordFits
  have word := load_eq fits
  rw [loaded] at word
  have value := congrArg BitVec.toNat (Option.some.inj word.symm)
  change (BitVec.ofNat (8 * 4) (leNat (bytesAt B ⟨address, 4⟩))).toNat = 0 at value
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordFits] at value
  cases bytes : bytesAt B ⟨address, 4⟩ with
  | nil => simp [bytes] at length
  | cons first rest =>
    rw [bytes, leNat_cons] at value
    have zero : first = 0 := UInt8.toNat.inj (by change first.toNat = 0; omega)
    have get := getElem?_bytesAt B ⟨address, 4⟩ 0
    rw [bytes, zero] at get
    have read : B.data[address]? = some 0 := by simpa using get.symm
    have index : address < B.size := by omega
    simpa [getElem?_pos B address index, ByteArray.getElem_eq_getElem_data,
      getElem?_pos B.data address (show address < B.data.size from index)] using read

/-- The known zero word in prepared memory gives an overlapping one-octet read. -/
theorem reactorPreparedZeroRead (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (address, mem) ∧
      Steps P host ⟨runtime, frame, vals [.i32 59328, .i32 59328] ++ [.plain (.call ⟨434⟩)]⟩
        ⟨runtime.setMem address
          { mem with bytes := Memory.writeSlice mem.bytes 59328 (Memory.encodeLE 8 0) },
          frame, [constI32 1]⟩ := by
  obtain ⟨before, _, base, baseFrame, baseMem, basePrepared, _, _, _, _, baseMapped, size, flag, _⟩ :=
    reactorDirectPreparation
  obtain ⟨runtime, frame, mem, address, prepared, mapped, effect⟩ := reactorPreparedReader P host
  have ⟨stores, frames⟩ := Prod.mk.inj (Option.some.inj (prepared.symm.trans basePrepared))
  have sameFrame := (Prod.mk.inj frames).1
  have resolve : runtime.mem? frame ⟨0⟩ = some (before.mems.length, baseMem) := by
    rw [stores, sameFrame]
    exact baseMapped
  have sameMem := (Prod.mk.inj (Option.some.inj (mapped.symm.trans resolve))).2
  have memSize : mem.bytes.size = 131072 := by
    rw [sameMem]
    exact size
  have loaded : Memory.load mem.bytes 59328 4 = some 0 := by
    rw [sameMem]
    exact flag
  have first := firstByteOfZeroWord (B := mem.bytes) (address := 59328) (by omega) loaded
  have found := GetVarintReaderSupport.viewByte _ _ _ first
  have read : Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) 59328 = some (0, 59329) := by
    simp [Varint.read?, Varint.readNat?, Varint.readAux?, found]
  refine ⟨runtime, frame, mem, address, prepared, mapped, ?_⟩
  exact effect (src := 59328) (dst := 59328) read (by change 59328 + 8 ≤ mem.bytes.size; omega)

#print axioms reactorPreparedZeroRead

end SqliteWasm
