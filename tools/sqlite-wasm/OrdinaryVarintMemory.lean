module

public import SqliteWasm.ThreeByteLoopMemory
import Silmaril.Wasm.Logic.Memory.Thms
import Mathlib.Data.Nat.Find

@[expose] public section

namespace SqliteWasm.OrdinaryVarint

open Silmaril.Wasm Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Execution
open Silmaril.Formats.Sqlite Silmaril.Wasm.Logic.Core
open ThreeByte (scratchAddress scratchAddress_eq scratchBytes outputBytes)
open ThreeByte.Symbolic (digit digits digitsMemory digitsSize loadInSlice digitFirst storeByte
  writeSlice_setHead sliceSize loadDisjointSlice writeSlice_append emptySlice)

/-- A positive input in the canonical base-128 interval for an ordinary width. -/
structure Width (x width : Nat) : Prop where
  positive : 0 < width
  ordinary : width ≤ 8
  lower : 128 ^ (width - 1) ≤ x
  upper : x < 128 ^ width

/-- In-bounds, disjoint output and scratch spans for the same width. -/
structure Buffers (B : ByteArray) (ptr sp : BitVec 32) (width : Nat) : Prop where
  stackSubtraction : 16 ≤ sp.toNat
  outputNoWrap : ptr.toNat + width ≤ 2 ^ 32
  outputInBounds : ptr.toNat + width ≤ B.size
  scratchInBounds : scratchAddress sp + width ≤ B.size
  disjoint : ptr.toNat + width ≤ scratchAddress sp ∨
    scratchAddress sp + width ≤ ptr.toNat

theorem Width.belowNine {x width : Nat} (h : Width x width) : x < 2 ^ 56 :=
  h.upper.trans_le (Nat.pow_le_pow_right (by decide) h.ordinary)

/-- Every value forwarded by the wrapper below the nine-byte threshold
has an ordinary width from three through eight. -/
theorem existsWidth (x : Nat) (lower : 16384 ≤ x) (upper : x < 2 ^ 56) :
    ∃ width, 3 ≤ width ∧ Width x width := by
  have existsBound : ∃ width : Nat, x < 128 ^ width := ⟨8, upper⟩
  let width := Nat.find existsBound
  have top : x < 128 ^ width := Nat.find_spec existsBound
  have bottom : 3 ≤ width := by
    by_contra! small
    have mono : 128 ^ width ≤ 128 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    have tooSmall : x < 16384 := top.trans_le mono
    omega
  exact ⟨width, bottom, by omega, Nat.find_min' existsBound (m := 8) upper,
    Nat.le_of_not_gt (Nat.find_min existsBound (show width - 1 < width by omega)), top⟩

private def payload (b : UInt8) : UInt8 := UInt8.ofNat (b.toNat % 128)

private def raw (x i : Nat) : UInt8 := UInt8.ofNat (x / 128 ^ i % 128)

private theorem payload_digit (x : Nat) :
    payload (UInt8.ofNat (x % 128 + 128)) = UInt8.ofNat (x % 128) := by
  unfold payload
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show x % 128 + 128 < 256 by omega),
    show (x % 128 + 128) % 128 = x % 128 by omega]

private theorem payload_small {x : Nat} (bound : x < 128) :
    payload (UInt8.ofNat x) = UInt8.ofNat x := by
  unfold payload
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show x < 256 by omega), Nat.mod_eq_of_lt bound]

private theorem raw_next (x i : Nat) : raw (x / 128) i = raw x (i + 1) := by
  unfold raw
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ']

private theorem seven_payload (fuel width x : Nat) (positive : 0 < width) (budget : width ≤ fuel)
    (lower : 128 ^ (width - 1) ≤ x) (upper : x < 128 ^ width) :
    (Varint.seven fuel x).map payload = ((List.range width).map (raw x)).reverse := by
  induction fuel generalizing width x with
  | zero => omega
  | succ fuel ih =>
    cases width with
    | zero => omega
    | succ width =>
      cases width with
      | zero =>
        have small : x < 128 := upper
        simp [Varint.seven, small, payload_small small, raw, Nat.mod_eq_of_lt small]
      | succ width =>
        have base : 128 ≤ x := by
          have mono : 128 ^ 1 ≤ 128 ^ (width + 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          exact mono.trans lower
        have lower' : 128 ^ ((width + 1) - 1) ≤ x / 128 := by
          apply (Nat.le_div_iff_mul_le (by decide)).2
          rw [← Nat.pow_succ]
          exact lower
        have upper' : x / 128 < 128 ^ (width + 1) := by
          apply (Nat.div_lt_iff_lt_mul (by decide)).2
          rwa [← Nat.pow_succ]
        have shift : (List.range (width + 1)).map (raw (x / 128)) =
            (List.range (width + 1)).map (fun i => raw x (i + 1)) :=
          List.map_congr_left fun i _ => raw_next x i
        rw [Varint.seven, ite_eq_right (Nat.not_lt.mpr base), List.map_append,
          ih (width + 1) (x / 128) (by omega) (by omega) lower' upper', shift, List.map_cons,
          List.map_nil, payload_digit]
        conv_rhs => rw [List.range_succ_eq_map]
        simp [raw, List.map_map, Function.comp_def]

/-- The emitted digit prefix has its continuation bit set at each index.
The finalized scratch image clears the bit on its first byte. -/
def scratchDigits (x width : Nat) : List UInt8 :=
  UInt8.ofNat (x % 128) :: (List.range (width - 1)).map (fun i => digit x (i + 1))

private theorem scratchDigitsLength (x width : Nat) (positive : 0 < width) :
    (scratchDigits x width).length = width := by
  simp [scratchDigits]
  omega

private theorem scratchDigitsAt (x width i : Nat) (index : i < (scratchDigits x width).length) :
    (scratchDigits x width)[i] = if i = 0 then UInt8.ofNat (x % 128) else digit x i := by
  cases i <;> simp [scratchDigits]

theorem scratchBytes_eq_digits (value : UInt64) (width : Nat) (h : Width value.toNat width) :
    scratchBytes value = ⟨(scratchDigits value.toNat width).toArray⟩ := by
  let x := value.toNat
  let core := Varint.seven 8 x
  have payloads := seven_payload 8 width x h.positive h.ordinary h.lower h.upper
  change core.map payload = _ at payloads
  have len : core.length = width := by
    simpa only [List.length_map, List.length_reverse, List.length_range] using congrArg List.length payloads
  apply ByteArray.ext
  apply Array.toList_inj.mp
  unfold scratchBytes Varint.encode
  dsimp only
  rw [ite_eq_left h.belowNine, Silmaril.Formats.Bytes.toList_ofList]
  change ((core.zipIdx.map _).reverse) = scratchDigits x width
  apply List.ext_getElem
  · simp [len, scratchDigitsLength _ _ h.positive]
  intro i ih jh
  rw [scratchDigitsAt _ _ i jh]
  have index : i < width := by simpa only [scratchDigitsLength _ _ h.positive] using jh
  have p := congrArg (fun bytes : List UInt8 => bytes[width - 1 - i]?) payloads
  rw [List.getElem?_eq_getElem (by simp [len]; omega),
    List.getElem?_eq_getElem (by simp; omega)] at p
  have digitAt := Option.some.inj p
  simp only [List.getElem_map, List.getElem_reverse, List.length_map,
    List.length_range, List.getElem_range, show width - 1 - (width - 1 - i) = i by omega] at digitAt
  simp only [List.getElem_reverse, List.length_map, List.length_zipIdx, List.getElem_map,
    List.getElem_zipIdx, Nat.zero_add, len]
  change (if width - 1 - i + 1 < core.length then _ else _) = _
  have payloadValue := congrArg UInt8.toNat digitAt
  have low : x / 128 ^ i % 128 < 128 := Nat.mod_lt _ (by decide)
  have asNat : core[width - 1 - i].toNat % 128 = x / 128 ^ i % 128 := by
    simpa only [payload, raw, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show x / 128 ^ i % 128 < 256 by omega),
      Nat.mod_eq_of_lt (show core[width - 1 - i].toNat % 128 < 256 by omega)] using payloadValue
  by_cases first : i = 0
  · have stop : ¬ width - 1 - i + 1 < core.length := by omega
    rw [ite_eq_right stop, ite_eq_left first, asNat, first]
    simp only [Nat.pow_zero, Nat.div_one]
  · have more : width - 1 - i + 1 < core.length := by omega
    rw [ite_eq_left more, ite_eq_right first, asNat]
    rfl

theorem ordinaryLength (value : UInt64) (width : Nat) (h : Width value.toNat width) :
    (Varint.encode value).data.size = width := by
  have length := congrArg ByteArray.size (scratchBytes_eq_digits value width h)
  change (Varint.encode value).toList.reverse.length = (scratchDigits value.toNat width).length at length
  rw [List.length_reverse, scratchDigitsLength _ _ h.positive] at length
  exact length

private def encoded (value : UInt64) : ByteArray := (Varint.encode value).data

def scratchMemory (B : ByteArray) (sp : BitVec 32) (value : UInt64) : ByteArray :=
  Memory.writeSlice B (scratchAddress sp) (scratchBytes value)

def copyMemory (B : ByteArray) (ptr sp : BitVec 32) (value : UInt64) (count : Nat) : ByteArray :=
  Memory.writeSlice (scratchMemory B sp value) ptr.toNat ((Varint.encode value).data.extract 0 count)

theorem scratchLength (value : UInt64) (width : Nat) (h : Width value.toNat width) :
    (scratchBytes value).size = width := by
  rw [scratchBytes_eq_digits value width h]
  exact scratchDigitsLength _ _ h.positive

private theorem digits_cons (x n : Nat) :
    digits x (n + 1) =
      ⟨⟨digit x 0 :: (List.range n).map (fun i => digit x (i + 1))⟩⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [digits, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Clear the continuation bit on the first stored digit, for an ordinary width. -/
theorem clearDigit (B : ByteArray) (ptr sp : BitVec 32) (value : UInt64) (width : Nat)
    (buffers : Buffers B ptr sp width) (w : Width value.toNat width) :
    let base := scratchAddress sp
    let mem := digitsMemory B sp.toNat value.toNat width
    stW 32 1 mem base (ldW 32 1 .unsigned mem base &&& 127#32) = scratchMemory B sp value := by
  have inBounds := buffers.scratchInBounds
  have memSize : (digitsMemory B sp.toNat value.toNat width).size = B.size :=
    ThreeByte.Symbolic.digitsMemorySize _ _ _ _ inBounds
  have read : ldW 32 1 .unsigned (digitsMemory B sp.toNat value.toNat width) (scratchAddress sp) =
      BitVec.ofNat 32 (digit value.toNat 0).toNat := by
    have bound : scratchAddress sp + (digits value.toNat width).size ≤ B.size := by
      rw [digitsSize]; exact inBounds
    have first : (digits value.toNat width).data.toList[0]? = some (digit value.toNat 0) := by
      cases width with
      | zero => have := w.positive; omega
      | succ n => rw [digits_cons]; rfl
    exact loadInSlice B _ _ 0 _ bound (by rw [digitsSize]; exact w.positive) first
  dsimp only
  rw [read, digitFirst, storeByte _ _ _ (by rw [memSize]; have := w.positive; omega)]
  have packed : ((BitVec.ofNat 32 (value.toNat % 128)).setWidth 8).toNat = value.toNat % 128 := by
    rw [BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [packed, scratchMemory, scratchBytes_eq_digits value width w]
  cases width with
  | zero => have := w.positive; omega
  | succ n =>
    change Memory.writeSlice (Memory.writeSlice B (scratchAddress sp) (digits value.toNat (n + 1)))
      (scratchAddress sp) ⟨#[UInt8.ofNat (value.toNat % 128)]⟩ = _
    rw [digits_cons, writeSlice_setHead (bound := by omega)]
    rfl

theorem copyMemorySize (B : ByteArray) (ptr sp : BitVec 32) (value : UInt64) (width j : Nat)
    (buffers : Buffers B ptr sp width) (w : Width value.toNat width) :
    (copyMemory B ptr sp value j).size = B.size := by
  have inner : (scratchMemory B sp value).size = B.size := by
    apply sliceSize
    rw [scratchLength value width w]
    exact buffers.scratchInBounds
  unfold copyMemory
  rw [sliceSize (bound := ?_), inner]
  rw [inner, ByteArray.size_extract, ordinaryLength value width w]
  have := buffers.outputInBounds
  omega

private theorem reverseDigits (value : UInt64) (width j : Nat)
    (w : Width value.toNat width) (index : j < width) :
    ∃ b : UInt8, (scratchBytes value).data.toList[width - 1 - j]? = some b ∧
      (encoded value).extract 0 (j + 1) = (encoded value).extract 0 j ++ ⟨#[b]⟩ := by
  let bytes := (Varint.encode value).toList
  have len : bytes.length = width := by
    exact ordinaryLength value width w
  let b := bytes[j]'(by omega)
  refine ⟨b, ?_, ?_⟩
  · change bytes.reverse[width - 1 - j]? = _
    rw [List.getElem?_eq_getElem (by simp [len]; omega)]
    simp only [List.getElem_reverse]
    have mirror : bytes.length - 1 - (width - 1 - j) = j := by omega
    simp [b, mirror]
  · apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      Nat.sub_zero, List.drop_zero, ByteArray.toList_data_append]
    change bytes.take (j + 1) = bytes.take j ++ [b]
    exact (List.take_append_getElem (l := bytes) (i := j) (by omega)).symm

/-- One iteration of the reverse copy reads the next scratch digit and extends the
output prefix. All earlier writes and all bytes outside the two ranges are fixed. -/
theorem copyIteration (B : ByteArray) (ptr sp : BitVec 32) (value : UInt64) (width j : Nat)
    (buffers : Buffers B ptr sp width) (w : Width value.toNat width) (index : j < width) :
    let mem := copyMemory B ptr sp value j
    stW 32 1 mem (ptr.toNat + j)
      (ldW 32 1 .unsigned mem (scratchAddress sp + (width - 1) - j)) =
        copyMemory B ptr sp value (j + 1) := by
  let base := scratchAddress sp
  let scratch := scratchMemory B sp value
  let prefixBytes := (encoded value).extract 0 j
  have scratchBound := buffers.scratchInBounds
  have outputBound := buffers.outputInBounds
  have scratchData := scratchLength value width w
  have scratchMem : scratch.size = B.size := sliceSize _ _ _ (by
    show base + (scratchBytes value).size ≤ B.size
    rw [scratchData]; exact scratchBound)
  have prefixSize : prefixBytes.size = j := by
    dsimp only [prefixBytes, encoded]
    rw [ByteArray.size_extract, ordinaryLength value width w]
    omega
  obtain ⟨byte, selectByte, further⟩ := reverseDigits value width j w index
  have wrote : ptr.toNat + prefixBytes.size ≤ scratch.size := by omega
  have canRead : base + (width - 1 - j) + 1 ≤ scratch.size := by omega
  have disjoint : Region.Disjoint ⟨ptr.toNat, prefixBytes.size⟩ ⟨base + (width - 1 - j), 1⟩ := by
    have separate := buffers.disjoint
    change ptr.toNat + width ≤ base ∨ base + width ≤ ptr.toNat at separate
    simp only [Region.Disjoint, Region.stop]
    omega
  have ready := loadDisjointSlice scratch prefixBytes ptr.toNat
    (base + (width - 1 - j)) wrote canRead disjoint
  have loaded := loadInSlice B (scratchBytes value) base (width - 1 - j) byte
    (by rw [scratchData]; exact scratchBound) (by rw [scratchData]; omega) selectByte
  have addr : scratchAddress sp + (width - 1) - j = base + (width - 1 - j) := by
    dsimp only [base]
    omega
  have size := copyMemorySize B ptr sp value width j buffers w
  dsimp only
  rw [addr]
  change stW 32 1 (Memory.writeSlice scratch ptr.toNat prefixBytes) (ptr.toNat + j)
    (ldW 32 1 .unsigned (Memory.writeSlice scratch ptr.toNat prefixBytes) (base + (width - 1 - j))) =
      Memory.writeSlice scratch ptr.toNat ((encoded value).extract 0 (j + 1))
  rw [ready]
  change ldW 32 1 .unsigned scratch (base + (width - 1 - j)) = _ at loaded
  rw [loaded, storeByte _ _ _ (show ptr.toNat + j + 1 ≤ (Memory.writeSlice scratch ptr.toNat prefixBytes).size by
      change ptr.toNat + j + 1 ≤ (copyMemory B ptr sp value j).size
      omega),
    further]
  have packed : ((BitVec.ofNat 32 byte.toNat).setWidth 8).toNat = byte.toNat := by
    rw [BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt byte.toNat_lt]
  rw [packed]
  rw [← writeSlice_append (bound := by
    change ptr.toNat + prefixBytes.size + 1 ≤ scratch.size
    omega), prefixSize]
  rw [UInt8.ofNat_toNat]

theorem copyDone (B : ByteArray) (ptr sp : BitVec 32) (value : UInt64) (width : Nat)
    (w : Width value.toNat width) :
    copyMemory B ptr sp value width = outputBytes B ptr sp value := by
  unfold copyMemory outputBytes scratchMemory
  rw [← ordinaryLength value width w]
  simp

theorem copyZero (B : ByteArray) (ptr sp : BitVec 32) (value : UInt64) :
    copyMemory B ptr sp value 0 = scratchMemory B sp value := by
  change Memory.writeSlice _ _ ((encoded value).extract 0 0) = _
  rw [ByteArray.extract_eq_empty_iff.mpr (Nat.zero_min _).le]
  exact emptySlice _ _

#print axioms existsWidth
#print axioms ordinaryLength
#print axioms scratchBytes_eq_digits
#print axioms clearDigit
#print axioms copyIteration
#print axioms copyDone
end SqliteWasm.OrdinaryVarint
