module

public import SqliteWasm.ThreeByteContract
public import Silmaril.Wasm.Auto2.VCGen.Defs
import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section

namespace SqliteWasm.ThreeByte.Symbolic

open Silmaril.Wasm Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Execution
open Silmaril.Formats.Sqlite Silmaril.Wasm.Logic.Core

/-! The two loop invariants track exact byte images after each prefix write. -/

def digit (x j : Nat) : UInt8 := UInt8.ofNat (x / 128 ^ j % 128 + 128)

def digits (x count : Nat) : ByteArray :=
  ⟨((List.range count).map (digit x)).toArray⟩

def digitsMemory (original : ByteArray) (sp x count : Nat) : ByteArray :=
  Memory.writeSlice original (sp - 10) (digits x count)

def radixValue (x : BitVec 32) : UInt64 := UInt64.ofNat x.toNat

def scratchMemory (original : ByteArray) (sp : BitVec 32) (x : BitVec 32) : ByteArray :=
  Memory.writeSlice original (scratchAddress sp) (scratchBytes (radixValue x))

def copyMemory (original : ByteArray) (ptr sp x : BitVec 32) (count : Nat) : ByteArray :=
  let output := (Varint.encode (radixValue x)).data
  Memory.writeSlice (scratchMemory original sp x) ptr.toNat (output.extract 0 count)

private theorem spliceAdjacent {α : Type} (memory first second : List α) (start : Nat)
    (bound : start + first.length + second.length ≤ memory.length) :
    Memory.spliceL (Memory.spliceL memory start first) (start + first.length) second =
      Memory.spliceL memory start (first ++ second) := by
  simp only [Memory.spliceL_eq, List.length_append]
  let written := memory.take start ++ first
  let suffix := memory.drop (start + first.length)
  have writtenLength : written.length = start + first.length := by
    simp [written, Nat.min_eq_left (show start ≤ memory.length by omega)]
  change (written ++ suffix).take (start + first.length) ++ second ++
    (written ++ suffix).drop (start + first.length + second.length) = _
  rw [List.take_left' writtenLength, ← List.drop_drop, List.drop_left' writtenLength]
  simp only [written, suffix, List.append_assoc, List.drop_drop, Nat.add_assoc]

private theorem writeSlice_append (B left right : ByteArray) (start : Nat)
    (bound : start + left.size + right.size ≤ B.size) :
    Memory.writeSlice (Memory.writeSlice B start left) (start + left.size) right =
      Memory.writeSlice B start (left ++ right) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change Memory.spliceL (Memory.spliceL B.data.toList start left.data.toList)
    (start + left.size) right.data.toList = Memory.spliceL B.data.toList start
    (left ++ right).data.toList
  rw [ByteArray.toList_data_append]
  exact spliceAdjacent _ _ _ start bound

private theorem spliceSetHead {α : Type} (memory rest : List α) (before after : α) (start : Nat)
    (bound : start ≤ memory.length) :
    Memory.spliceL (Memory.spliceL memory start (before :: rest)) start [after] =
      Memory.spliceL memory start (after :: rest) := by
  induction start generalizing memory with
  | zero => simp [Memory.spliceL]
  | succ start ih =>
    cases memory with
    | nil => simp at bound
    | cons head memory =>
      exact congrArg (List.cons head) (ih memory (by simpa using bound))

private theorem writeSlice_setHead (memory : ByteArray) (rest : List UInt8) (before after : UInt8) (start : Nat)
    (bound : start ≤ memory.size) :
    Memory.writeSlice (Memory.writeSlice memory start ⟨⟨before :: rest⟩⟩) start ⟨#[after]⟩ =
      Memory.writeSlice memory start ⟨⟨after :: rest⟩⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact spliceSetHead _ _ _ _ _ bound

private theorem packedContinuation (x : BitVec 64) :
    ((x.setWidth 32 ||| 128#32).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 (x.toNat % 128 + 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.or_mod_two_pow]
  change (x.toNat % 4294967296 % 256 ||| 128) = (x.toNat % 128 + 128) % 256
  have lowByte : x.toNat % 4294967296 % 256 = x.toNat % 256 := by omega
  rw [lowByte, Nat.mod_eq_of_lt (show x.toNat % 128 + 128 < 256 by omega)]
  have bit := Nat.or_two_pow_eq_add_of_lt (n := 7) (Nat.mod_lt x.toNat (by decide))
  have cases : x.toNat % 256 = x.toNat % 128 ∨ x.toNat % 256 = x.toNat % 128 + 128 :=
    by omega
  rcases cases with clear | set
  · rw [clear]
    exact bit
  · calc
      _ = (x.toNat % 128 ||| 128) ||| 128 := by rw [set, bit]
      _ = _ := by rw [Nat.or_assoc, show (128 : Nat) ||| 128 = 128 from rfl, bit]

private theorem emptySlice (B : ByteArray) (p : Nat) :
    Memory.writeSlice B p ⟨#[]⟩ = B := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [Memory.writeSlice, Memory.spliceL_eq]

private theorem sliceSize (B D : ByteArray) (p : Nat) (bound : p + D.size ≤ B.size) :
    (Memory.writeSlice B p D).size = B.size :=
  Memory.writeBytes_size B D _ p (by simp only [Memory.writeBytes, ite_eq_left bound])

theorem storeSize (B : ByteArray) (p : Nat) (w : BitVec 32) :
    (stW 32 1 B p w).size = B.size := by
  unfold stW
  cases result : Memory.store B p (count := 1) (w.setWidth 8) with
  | none => rfl
  | some bytes => exact Memory.writeBytes_size B _ _ p result

private theorem storeByte (B : ByteArray) (p : Nat) (w : BitVec 32) (bound : p + 1 ≤ B.size) :
    stW 32 1 B p w = Memory.writeSlice B p ⟨#[UInt8.ofNat (w.setWidth 8).toNat]⟩ := by
  simp only [stW, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bound,
    Option.getD_some]
  rfl

private theorem digitsSize (x j : Nat) : (digits x j).size = j := by
  simp [digits, ByteArray.size]

private theorem digitsSucc (x j : Nat) :
    digits x (j + 1) = digits x j ++ ⟨#[digit x j]⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [digits, List.range_succ]

theorem digitsMemorySize (B : ByteArray) (sp x j : Nat)
    (bound : sp - 10 + j ≤ B.size) : (digitsMemory B sp x j).size = B.size := by
  apply sliceSize
  simpa only [digitsSize] using bound

theorem noWrapScratch (sp idx : BitVec 32) (stack : 16 ≤ sp.toNat)
    (index : idx.toNat ≤ 3) :
    (sp - 16#32 + 6#32 + idx).toNat = scratchAddress sp + idx.toNat := by
  have word : (sp - 16#32 + 6#32).toNat = scratchAddress sp := scratchAddress_eq sp stack
  have ceiling := sp.isLt
  rw [BitVec.toNat_add_of_lt (by rw [word, scratchAddress]; omega), word]

theorem scratchBase (sp : BitVec 32) (stack : 16 ≤ sp.toNat) :
    (sp - 16#32).toNat + 6 = scratchAddress sp := by
  rw [BitVec.toNat_sub_of_le (by exact stack), scratchAddress]
  change sp.toNat - 16 + 6 = sp.toNat - 10
  omega

theorem digitIteration (B : ByteArray) (sp : BitVec 32) (x j : Nat) (w : BitVec 64)
    (remaining : w.toNat = x / 128 ^ j) (bound : scratchAddress sp + j + 1 ≤ B.size) :
    stW 32 1 (digitsMemory B sp.toNat x j) (scratchAddress sp + j)
      (w.setWidth 32 ||| 128#32) = digitsMemory B sp.toNat x (j + 1) := by
  have inBounds : scratchAddress sp + j + 1 ≤ (digitsMemory B sp.toNat x j).size := by
    rw [digitsMemorySize (bound := by unfold scratchAddress at bound; omega)]
    exact bound
  rw [storeByte _ _ _ inBounds, packedContinuation, BitVec.toNat_ofNat]
  have byteFits : w.toNat % 128 + 128 < 256 := by omega
  rw [Nat.mod_eq_of_lt (show w.toNat % 128 + 128 < 2 ^ 8 by exact byteFits), remaining]
  change Memory.writeSlice (Memory.writeSlice B (scratchAddress sp) (digits x j))
    (scratchAddress sp + j) ⟨#[digit x j]⟩ =
    Memory.writeSlice B (scratchAddress sp) (digits x (j + 1))
  have spliceBound : scratchAddress sp + (digits x j).size + (⟨#[digit x j]⟩ : ByteArray).size ≤ B.size := by
    rw [digitsSize]
    exact bound
  rw [digitsSucc, ← writeSlice_append (bound := spliceBound), digitsSize]

theorem wrapNat (x : BitVec 64) (fits : x.toNat < 4294967296) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits]

theorem remainingShift (x : BitVec 64) (j : Nat) (w : BitVec 64)
    (remaining : w.toNat = x.toNat / 128 ^ j) :
    (w >>> 7).toNat = x.toNat / 128 ^ (j + 1) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, remaining, Nat.div_div_eq_div_mul]
  change x.toNat / (128 ^ j * 128) = _
  rw [Nat.pow_succ]

theorem digitBranch (x : BitVec 64) (j : Nat) (w : BitVec 64)
    (lower : 16384 ≤ x.toNat) (upper : x.toNat < 2097152) (idx : j < 3)
    (remaining : w.toNat = x.toNat / 128 ^ j) :
    ((if 127 < w.toNat then (1 : BitVec 32) else 0) ≠ 0 ↔ j < 2) ∧
      ((if 127 < w.toNat then (1 : BitVec 32) else 0) = 0 ↔ j = 2) := by
  have modes : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  split <;> rename_i comparison <;>
    rcases modes with rfl | rfl | rfl <;>
    simp_all <;> omega

theorem countNext (idx : BitVec 32) (bound : idx.toNat < 3) :
    (idx + 1#32).toNat = idx.toNat + 1 :=
  BitVec.toNat_add_of_lt (by change idx.toNat + 1 < 2 ^ 32; omega)

private theorem loadInSlice (B D : ByteArray) (p j : Nat) (byte : UInt8)
    (bound : p + D.size ≤ B.size) (index : j < D.size)
    (selected : D.data.toList[j]? = some byte) :
    ldW 32 1 .unsigned (Memory.writeSlice B p D) (p + j) = BitVec.ofNat 32 byte.toNat := by
  have wrote : Memory.writeBytes B p D = some (Memory.writeSlice B p D) :=
    by simp only [Memory.writeBytes, ite_eq_left bound]
  have contents : bytesAt D ⟨j, 1⟩ = [byte] := by
    apply List.ext_getElem?
    intro i
    cases i <;> simp [getElem?_bytesAt, selected]
  have read := load_eq (B := Memory.writeSlice B p D) (a := p + j) (n := 1)
    (by rw [sliceSize _ _ _ bound]; omega)
  rw [bytesAt_writeBytes_inside wrote (by
    simp only [Region.Contains, Region.stop]
    omega), show p + j - p = j by omega, contents] at read
  unfold ldW rd
  rw [read, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [leNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hb := byte.toNat_lt
  exact congrArg (fun n => n % 2 ^ 32) (Nat.mod_eq_of_lt (by exact hb))

theorem toNat_radixValue (x : BitVec 32) : (radixValue x).toNat = x.toNat := by
  have bound := x.isLt
  change x.toNat < 4294967296 at bound
  rw [radixValue, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

private theorem digitFirst (x : Nat) :
    (BitVec.ofNat 32 (digit x 0).toNat &&& 127#32) =
      BitVec.ofNat 32 (x % 128) := by
  have h : x % 128 + 128 < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [digit, Nat.pow_zero, Nat.div_one, UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt h, BitVec.toNat_and, BitVec.toNat_ofNat]
  have fits1 : x % 128 + 128 < 2 ^ 32 := by omega
  have fits2 : x % 128 < 2 ^ 32 := by omega
  simp only [Nat.mod_eq_of_lt fits1, Nat.mod_eq_of_lt fits2]
  change (x % 128 + 128) &&& (2 ^ 7 - 1) = x % 128
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem digitsThree (x : Nat) :
    digits x 3 = ⟨#[digit x 0, digit x 1, digit x 2]⟩ := rfl

theorem clearDigit (B : ByteArray) (ptr sp x : BitVec 32)
    (buffers : Buffers B ptr sp) (lower : 16384 ≤ x.toNat) (upper : x.toNat < 2097152) :
    let base := scratchAddress sp
    let mem := digitsMemory B sp.toNat x.toNat 3
    stW 32 1 mem base (ldW 32 1 .unsigned mem base &&& 127#32) =
      scratchMemory B sp x := by
  have inBounds := buffers.scratchInBounds
  have memSize : (digitsMemory B sp.toNat x.toNat 3).size = B.size :=
    digitsMemorySize _ _ _ _ inBounds
  have load : ldW 32 1 .unsigned (digitsMemory B sp.toNat x.toNat 3) (scratchAddress sp) =
      BitVec.ofNat 32 (digit x.toNat 0).toNat := by
    have bound : scratchAddress sp + (digits x.toNat 3).size ≤ B.size := by
      rw [digitsSize]; exact inBounds
    exact loadInSlice B _ _ 0 _ bound (by rw [digitsSize]; decide) rfl
  dsimp only
  rw [load, digitFirst, storeByte _ _ _ (by rw [memSize]; omega)]
  have packed : ((BitVec.ofNat 32 (x.toNat % 128)).setWidth 8).toNat = x.toNat % 128 := by
    rw [BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [packed, scratchMemory, scratchBytes_eq (radixValue x)
    (by rwa [toNat_radixValue]) (by rwa [toNat_radixValue])]
  simp only [toNat_radixValue]
  unfold digitsMemory
  rw [digitsThree]
  have cr := writeSlice_setHead B [digit x.toNat 1, digit x.toNat 2] (digit x.toNat 0)
    (UInt8.ofNat (x.toNat % 128)) (scratchAddress sp) (by omega)
  have hi : x.toNat / 16384 % 128 = x.toNat / 16384 := Nat.mod_eq_of_lt (by omega)
  change Memory.writeSlice
    (Memory.writeSlice B (scratchAddress sp) ⟨⟨[digit x.toNat 0, digit x.toNat 1, digit x.toNat 2]⟩⟩)
    (scratchAddress sp) ⟨#[UInt8.ofNat (x.toNat % 128)]⟩ = _
  rw [cr]
  change Memory.writeSlice B (scratchAddress sp)
    ⟨⟨[UInt8.ofNat (x.toNat % 128), digit x.toNat 1,
      UInt8.ofNat (x.toNat / 16384 % 128 + 128)]⟩⟩ = _
  rw [hi]
  rfl

private def encoded (x : BitVec 32) : ByteArray := (Varint.encode (radixValue x)).data

private theorem encodedThree (x : BitVec 32) (lower : 16384 ≤ x.toNat)
    (upper : x.toNat < 2097152) :
    encoded x = ⟨#[UInt8.ofNat (x.toNat / 16384 + 128),
      UInt8.ofNat (x.toNat / 128 % 128 + 128), UInt8.ofNat (x.toNat % 128)]⟩ := by
  rw [encoded, encode_three (radixValue x) (by rwa [toNat_radixValue]) (by rwa [toNat_radixValue])]
  simp only [toNat_radixValue]
  rfl

private theorem scratchThree (x : BitVec 32) (lower : 16384 ≤ x.toNat)
    (upper : x.toNat < 2097152) :
    scratchBytes (radixValue x) = ⟨#[UInt8.ofNat (x.toNat % 128),
      UInt8.ofNat (x.toNat / 128 % 128 + 128), UInt8.ofNat (x.toNat / 16384 + 128)]⟩ := by
  rw [scratchBytes_eq (radixValue x) (by rwa [toNat_radixValue]) (by rwa [toNat_radixValue])]
  simp only [toNat_radixValue]

private theorem encodedSize (x : BitVec 32) (lower : 16384 ≤ x.toNat)
    (upper : x.toNat < 2097152) : (encoded x).size = 3 := by
  rw [encodedThree x lower upper]
  rfl

private theorem scratchSize (x : BitVec 32) (lower : 16384 ≤ x.toNat)
    (upper : x.toNat < 2097152) : (scratchBytes (radixValue x)).size = 3 := by
  rw [scratchThree x lower upper]
  rfl

theorem copyMemorySize (B : ByteArray) (ptr sp x : BitVec 32) (j : Nat)
    (buffers : Buffers B ptr sp) (lower : 16384 ≤ x.toNat) (upper : x.toNat < 2097152) :
    (copyMemory B ptr sp x j).size = B.size := by
  have inner : (scratchMemory B sp x).size = B.size := by
    apply sliceSize
    rw [scratchSize x lower upper]
    exact buffers.scratchInBounds
  unfold copyMemory
  change (Memory.writeSlice (scratchMemory B sp x) ptr.toNat ((encoded x).extract 0 j)).size = _
  rw [sliceSize (bound := ?_), inner]
  rw [inner, ByteArray.size_extract, encodedSize x lower upper]
  have := buffers.outputInBounds
  omega

private theorem loadDisjointSlice (B D : ByteArray) (dst src : Nat)
    (wrote : dst + D.size ≤ B.size) (read : src + 1 ≤ B.size)
    (disjoint : Region.Disjoint ⟨dst, D.size⟩ ⟨src, 1⟩) :
    ldW 32 1 .unsigned (Memory.writeSlice B dst D) src = ldW 32 1 .unsigned B src := by
  have hs := sliceSize B D dst wrote
  have hwrite : Memory.writeBytes B dst D = some (Memory.writeSlice B dst D) :=
    by simp only [Memory.writeBytes, ite_eq_left wrote]
  unfold ldW rd
  rw [load_eq (B := Memory.writeSlice B dst D) (by omega), load_eq read,
    bytesAt_writeBytes_disjoint hwrite disjoint]

private theorem reverseDigits (x : BitVec 32) (j : Nat) (index : j < 3)
    (lower : 16384 ≤ x.toNat) (upper : x.toNat < 2097152) :
    ∃ b : UInt8, (scratchBytes (radixValue x)).data.toList[2 - j]? = some b ∧
      (encoded x).extract 0 (j + 1) = (encoded x).extract 0 j ++ ⟨#[b]⟩ := by
  rw [scratchThree x lower upper, encodedThree x lower upper]
  have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩

theorem copyIteration (B : ByteArray) (ptr sp x : BitVec 32) (j : Nat) (index : j < 3)
    (buffers : Buffers B ptr sp) (lower : 16384 ≤ x.toNat) (upper : x.toNat < 2097152) :
    let mem := copyMemory B ptr sp x j
    stW 32 1 mem (ptr.toNat + j)
      (ldW 32 1 .unsigned mem (scratchAddress sp + 2 - j)) =
        copyMemory B ptr sp x (j + 1) := by
  let base := scratchAddress sp
  let scratch := scratchMemory B sp x
  let prefixBytes := (encoded x).extract 0 j
  have scratchBound := buffers.scratchInBounds
  have outputBound := buffers.outputInBounds
  have scratchData := scratchSize x lower upper
  have scratchMem : scratch.size = B.size := sliceSize _ _ _ (by
    show base + (scratchBytes (radixValue x)).size ≤ B.size
    rw [scratchData]; exact scratchBound)
  have prefixSize : prefixBytes.size = j := by
    dsimp only [prefixBytes]
    rw [ByteArray.size_extract, encodedSize x lower upper]
    omega
  obtain ⟨byte, selectByte, further⟩ := reverseDigits x j index lower upper
  have wrote : ptr.toNat + prefixBytes.size ≤ scratch.size := by omega
  have canRead : base + (2 - j) + 1 ≤ scratch.size := by omega
  have disjoint : Region.Disjoint ⟨ptr.toNat, prefixBytes.size⟩ ⟨base + (2 - j), 1⟩ := by
    have separate := buffers.disjoint
    change ptr.toNat + 3 ≤ base ∨ base + 3 ≤ ptr.toNat at separate
    simp only [Region.Disjoint, Region.stop]
    omega
  have ready := loadDisjointSlice scratch prefixBytes ptr.toNat (base + (2 - j)) wrote canRead disjoint
  have loaded := loadInSlice B (scratchBytes (radixValue x)) base (2 - j) byte
    (by rw [scratchData]; exact scratchBound) (by rw [scratchData]; omega) selectByte
  have addr : scratchAddress sp + 2 - j = base + (2 - j) := by dsimp only [base]; omega
  have size := copyMemorySize B ptr sp x j buffers lower upper
  dsimp only
  rw [addr]
  change stW 32 1 (Memory.writeSlice scratch ptr.toNat prefixBytes) (ptr.toNat + j)
    (ldW 32 1 .unsigned (Memory.writeSlice scratch ptr.toNat prefixBytes) (base + (2 - j))) =
      Memory.writeSlice scratch ptr.toNat ((encoded x).extract 0 (j + 1))
  rw [ready]
  change ldW 32 1 .unsigned scratch (base + (2 - j)) = _ at loaded
  rw [loaded, storeByte _ _ _ (show ptr.toNat + j + 1 ≤ (Memory.writeSlice scratch ptr.toNat prefixBytes).size by
      change ptr.toNat + j + 1 ≤ (copyMemory B ptr sp x j).size
      omega),
    further]
  have packed : ((BitVec.ofNat 32 byte.toNat).setWidth 8).toNat = byte.toNat := by
    rw [BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt byte.toNat_lt]
  rw [packed]
  rw [← writeSlice_append (bound := by
    change ptr.toNat + prefixBytes.size + 1 ≤ scratch.size
    omega), prefixSize]
  rw [UInt8.ofNat_toNat]

theorem copyDone (B : ByteArray) (ptr sp x : BitVec 32)
    (lower : 16384 ≤ x.toNat) (upper : x.toNat < 2097152) :
    copyMemory B ptr sp x 3 = outputBytes B ptr sp (radixValue x) := by
  unfold copyMemory outputBytes scratchMemory
  change Memory.writeSlice _ _ ((encoded x).extract 0 3) = Memory.writeSlice _ _ (encoded x)
  rw [← encodedSize x lower upper]
  simp

theorem copyZero (B : ByteArray) (ptr sp x : BitVec 32) :
    copyMemory B ptr sp x 0 = scratchMemory B sp x := by
  change Memory.writeSlice _ _ ((encoded x).extract 0 0) = _
  rw [ByteArray.extract_eq_empty_iff.mpr (Nat.zero_min _).le]
  exact emptySlice _ _

theorem digitsMemory_zero (B : ByteArray) (sp x : Nat) :
    digitsMemory B sp x 0 = B :=
  emptySlice B (sp - 10)

end SqliteWasm.ThreeByte.Symbolic
