module

public import SqliteWasm.OrdinaryVarintHelper
import Silmaril.Wasm.Auto2.VCGen.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

namespace SqliteWasm.NineByteVarint

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (CGlobalType Expand Ty)
open SqliteWasmArtifact
open ThreeByte (args callFrame activation putVarint_forward)
open ThreeByte.Symbolic (quotedHelper packedContinuation storeByte sliceSize reachExit singleI32)
open OrdinaryVarint (joinHalves joinSplit splitWord u64OfNat helperSpec helperSteps_of_vcs)

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Wasm computes the last byte address as an effective address at immediate offset
eight. Only the seven preceding address increments can wrap i32 addition. -/
structure Bounds (B : ByteArray) (ptr : BitVec 32) : Prop where
  loopNoWrap : ptr.toNat + 8 ≤ 2 ^ 32
  outputInBounds : ptr.toNat + 9 ≤ B.size

/-- The nine-byte path has one output write in the final store specification. -/
def outputBytes (B : ByteArray) (ptr : BitVec 32) (value : UInt64) : ByteArray :=
  Memory.writeSlice B ptr.toNat (Varint.encode value).data

private def digit (x j : Nat) : UInt8 :=
  UInt8.ofNat (x / 2 ^ (8 + 7 * (7 - j)) % 128 + 128)

private theorem encoded (value : UInt64) (wide : 2 ^ 56 ≤ value.toNat) :
    (Varint.encode value).toList =
      (List.range 8).map (digit value.toNat) ++ [UInt8.ofNat (value.toNat % 256)] := by
  rw [Varint.encode, ite_eq_right (Nat.not_lt.mpr wide), Silmaril.Formats.Bytes.toList_ofList]
  rfl

theorem encodedLength (value : UInt64) (wide : 2 ^ 56 ≤ value.toNat) :
    (Varint.encode value).length = 9 := by
  rw [Silmaril.Formats.Bytes.length_eq_toList_length, encoded value wide]
  rfl

private def suffix (value : UInt64) (j : Nat) : ByteArray :=
  ⟨((Varint.encode value).toList.drop j).toArray⟩

private def written (B : ByteArray) (ptr : BitVec 32) (value : UInt64) (j : Nat) : ByteArray :=
  Memory.writeSlice B (ptr.toNat + j) (suffix value j)

private theorem suffixSize (value : UInt64) (wide : 2 ^ 56 ≤ value.toNat) (j : Nat) :
    (suffix value j).size = 9 - j := by
  have length := encodedLength value wide
  rw [Silmaril.Formats.Bytes.length_eq_toList_length] at length
  change ((Varint.encode value).toList.drop j).length = _
  rw [List.length_drop, length]

private theorem writtenSize (B : ByteArray) (ptr : BitVec 32) (value : UInt64) (j : Nat)
    (wide : 2 ^ 56 ≤ value.toNat) (bound : ptr.toNat + 9 ≤ B.size) (idx : j ≤ 9) :
    (written B ptr value j).size = B.size := by
  apply sliceSize
  rw [suffixSize value wide j]
  omega

private theorem suffixLast (value : UInt64) (wide : 2 ^ 56 ≤ value.toNat) :
    suffix value 8 = ⟨#[UInt8.ofNat (value.toNat % 256)]⟩ := by
  unfold suffix
  rw [encoded value wide, List.drop_left' (by simp)]

private theorem seed (B : ByteArray) (ptr : BitVec 32) (word : BitVec 64)
    (wide : 2 ^ 56 ≤ word.toNat) (bound : ptr.toNat + 9 ≤ B.size) :
    stW 64 1 B (ptr.toNat + 8) word = written B ptr (UInt64.ofNat word.toNat) 8 := by
  unfold written
  rw [suffixLast _ (by rwa [u64OfNat]), u64OfNat]
  simp only [stW, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bound,
    Option.getD_some, BitVec.toNat_setWidth]
  rfl

private theorem splicePrepend {α : Type} (memory tailBytes : List α) (p : Nat) (b : α)
    (bound : p < memory.length) :
    Memory.spliceL (Memory.spliceL memory (p + 1) tailBytes) p [b] =
      Memory.spliceL memory p (b :: tailBytes) := by
  induction p generalizing memory with
  | zero =>
    cases memory with
    | nil => simp at bound
    | cons head tail => simp [Memory.spliceL]
  | succ p ih =>
    cases memory with
    | nil => simp at bound
    | cons head tail =>
      exact congrArg (List.cons head) (ih tail (by simpa using bound))

private theorem writePrepend (B rest : ByteArray) (p : Nat) (b : UInt8) (bound : p < B.size) :
    Memory.writeSlice (Memory.writeSlice B (p + 1) rest) p ⟨#[b]⟩ =
      Memory.writeSlice B p (⟨#[b]⟩ ++ rest) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change Memory.spliceL (Memory.spliceL B.data.toList (p + 1) rest.data.toList)
    p [b] = Memory.spliceL B.data.toList p ((⟨#[b]⟩ : ByteArray) ++ rest).data.toList
  rw [ByteArray.toList_data_append]
  exact splicePrepend _ _ _ _ bound

private theorem suffixStep (value : UInt64) (wide : 2 ^ 56 ≤ value.toNat) (j : Nat) (idx : j < 8) :
    suffix value j = ⟨#[digit value.toNat j]⟩ ++ suffix value (j + 1) := by
  have length := encodedLength value wide
  rw [Silmaril.Formats.Bytes.length_eq_toList_length] at length
  have pick : (Varint.encode value).toList[j]? = some (digit value.toNat j) := by
    rw [encoded value wide, List.getElem?_append_left (by simpa using idx)]
    simp [idx]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.toList_data_append]
  change (Varint.encode value).toList.drop j = _ :: (Varint.encode value).toList.drop (j + 1)
  rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.getElem?_eq_getElem (by omega)] at pick
  rw [Option.some.inj pick]

private theorem digitDiv (j : Nat) : 256 * 128 ^ (7 - j) = 2 ^ (8 + 7 * (7 - j)) := by
  rw [Nat.pow_add, Nat.pow_mul]

private theorem iteration (B : ByteArray) (ptr : BitVec 32) (value : UInt64) (j : Nat)
    (wide : 2 ^ 56 ≤ value.toNat) (bound : ptr.toNat + 9 ≤ B.size) (idx : j < 8)
    (word : BitVec 64) (remaining : word.toNat = value.toNat / (256 * 128 ^ (7 - j))) :
    stW 32 1 (written B ptr value (j + 1)) (ptr.toNat + j) (word.setWidth 32 ||| 128#32) =
      written B ptr value j := by
  have size := writtenSize B ptr value (j + 1) wide bound (by omega)
  have destination : ptr.toNat + j + 1 ≤ (written B ptr value (j + 1)).size := by omega
  rw [storeByte _ _ _ destination, packedContinuation, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show word.toNat % 128 + 128 < 2 ^ 8 by omega), remaining, digitDiv]
  change Memory.writeSlice (written B ptr value (j + 1)) (ptr.toNat + j)
    ⟨#[digit value.toNat j]⟩ = written B ptr value j
  unfold written
  rw [← Nat.add_assoc, writePrepend _ _ _ _ (by omega), suffixStep value wide j idx]

private theorem writtenZero (B : ByteArray) (ptr : BitVec 32) (value : UInt64) :
    written B ptr value 0 = outputBytes B ptr value := rfl

#print axioms encodedLength

private def assumptions (_ : Nat) (B : ByteArray) : List (BitVec 32) → Prop
  | [ptr, lo, hi] => 2 ^ 56 ≤ joinHalves lo hi ∧ Bounds B ptr
  | _ => False

private def relations (tag : Nat) (initial mem : ByteArray) (args : List (BitVec 32)) : Prop :=
  match tag, args with
  | 0, [ptr, j, lo, hi, leftLo, leftHi] =>
    j.toNat < 8 ∧ joinHalves leftLo leftHi = joinHalves lo hi / (256 * 128 ^ (7 - j.toNat)) ∧
      mem = written initial ptr (UInt64.ofNat (joinHalves lo hi)) (j.toNat + 1)
  | 1, [ptr, lo, hi] =>
    mem = outputBytes initial ptr (UInt64.ofNat (joinHalves lo hi))
  | _, _ => False

private def model : Fns := { pr := assumptions, pr2 := relations }

private def initialValue : List (Tm .i32) := splitWord (.var .i64 1)

private def symPre : Fm := .pr 0 (.v 0) (.var .i32 0 :: initialValue)

private def symPost : Fm :=
  .and (.rel .eq (.loc .i32 0) (.lit .i32 9))
    (.and (.rel .eq (.loc .i32 1) (.var .i32 2))
      (.pr2 1 (.v 0) .cur (.var .i32 0 :: initialValue)))

private def invariant : Fm :=
  .pr2 0 (.v 0) .cur ([.var .i32 0, .loc .i32 3] ++ initialValue ++ splitWord (.loc .i64 1))

private def spec : FnSpec :=
  helperSpec symPre symPost [.not .tt, .not .tt, invariant]
    [.lit .i32 0, .lit .i32 0, .loc .i32 3]

private def generated : List Fm := genFunc spec quotedHelper 128

private theorem loopAddress (B : ByteArray) (ptr j : BitVec 32) (bounds : Bounds B ptr)
    (index : j.toNat < 8) : (ptr + j).toNat = ptr.toNat + j.toNat := by
  apply BitVec.toNat_add_of_lt
  have safe := bounds.loopNoWrap
  omega

private theorem previousCount (j : BitVec 32) (positive : 0 < j.toNat) :
    (j + 4294967295#32).toNat = j.toNat - 1 := by
  rw [show j + 4294967295#32 = j - 1#32 from (BitVec.sub_eq_add_neg j 1#32).symm,
    BitVec.toNat_sub_of_le (by exact positive)]
  rfl

private theorem countPositive (j : BitVec 32) (branch : j + 4294967295#32 ≠ 4294967295#32) :
    0 < j.toNat := by
  by_contra! zero
  have equal : j = 0#32 := BitVec.eq_of_toNat_eq (by
    change j.toNat = 0
    omega)
  exact branch (by simp [equal])

private theorem countZero (j : BitVec 32) (branch : j + 4294967295#32 = 4294967295#32) :
    j.toNat = 0 := by
  by_contra! nonzero
  have prev := previousCount j (by omega)
  rw [branch] at prev
  have bound := j.isLt
  change 4294967295 = j.toNat - 1 at prev
  omega

private theorem shiftNext (x word : BitVec 64) (j : Nat) (positive : 0 < j) (index : j < 8)
    (remaining : word.toNat = x.toNat / (256 * 128 ^ (7 - j))) :
    (word >>> 7).toNat = x.toNat / (256 * 128 ^ (7 - (j - 1))) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, remaining, Nat.div_div_eq_div_mul]
  change x.toNat / ((256 * 128 ^ (7 - j)) * 128) = _
  rw [show 7 - (j - 1) = (7 - j) + 1 by omega, Nat.pow_succ, Nat.mul_assoc]

private theorem valid : AllValid model generated := by
  vcgen4_reduce
  vcgen4_den
  simp only [IntType.width, model, relations, assumptions, joinSplit]
  and_intros
  all_goals vcgen4_vars
  all_goals intro h
  all_goals repeat' cases_type And
  all_goals subst_vars
  all_goals try simp only [not_not, Nat.add_zero, BitVec.toNat_ofNat] at *
  all_goals try omega
  all_goals have bounds : Bounds M0 v0 := by assumption
  all_goals have wide : 2 ^ 56 ≤ w1.toNat := by assumption
  all_goals have wideValue : 2 ^ 56 ≤ (UInt64.ofNat w1.toNat).toNat := by rwa [u64OfNat]
  all_goals have inBounds := bounds.outputInBounds
  · exact inBounds
  · change 7 < 8 ∧ (w1 >>> 8).toNat = w1.toNat / 256 ∧
      stW 64 1 M0 (v0.toNat + 8) w1 = written M0 v0 (UInt64.ofNat w1.toNat) 8
    refine ⟨by decide, ?_, seed _ _ _ wide inBounds⟩
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · have index : v10.toNat < 8 := by assumption
    rw [loopAddress _ _ _ bounds index, writtenSize _ _ _ _ wideValue inBounds (by omega)]
    omega
  · have index : v10.toNat < 8 := by assumption
    have positive := countPositive v10 (by assumption)
    have rem : w8.toNat = w1.toNat / (256 * 128 ^ (7 - v10.toNat)) := by assumption
    rw [previousCount v10 positive]
    refine ⟨by omega, shiftNext w1 w8 _ positive index rem, ?_⟩
    rw [loopAddress _ _ _ bounds index, show v10.toNat - 1 + 1 = v10.toNat by omega]
    exact iteration _ _ _ _ wideValue inBounds index w8 (rem.trans (by rw [u64OfNat]))
  · rw [previousCount v10 (countPositive v10 (by assumption))]
    have positive := countPositive v10 (by assumption)
    omega
  · have index : v10.toNat < 8 := by assumption
    have rem : w8.toNat = w1.toNat / (256 * 128 ^ (7 - v10.toNat)) := by assumption
    rw [loopAddress _ _ _ bounds index,
      iteration _ _ _ _ wideValue inBounds index w8 (rem.trans (by rw [u64OfNat])),
      countZero v10 (by assumption), writtenZero]

#print axioms valid

/-- The quoted helper's fast path writes the nine-byte Lean encoding and preserves
all other memory, the globals, and the caller frame. -/
theorem helper_nineByte {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (s : Store H) (caller : Frame) (callee : ModuleInst) (ptr sp : BitVec 32)
    (value : UInt64) (address globalAddress : Nat) (mem : MemInst) (globalType : CGlobalType)
    (wide : 2 ^ 56 ≤ value.toNat)
    (mapped : s.mem? (callFrame callee quotedHelper ptr value) ⟨0⟩ = some (address, mem))
    (global : s.global? (callFrame callee quotedHelper ptr value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 sp⟩))
    (bounds : Bounds mem.bytes ptr) :
    Steps P host ⟨s, caller, [activation callee quotedHelper ptr value]⟩
      ⟨s.setMem address { mem with bytes := outputBytes mem.bytes ptr value }, caller, [constI32 9]⟩ := by
  refine helperSteps_of_vcs model symPre symPost _ _ (show spec.wellScoped = true by kernel_rfl)
    valid s caller callee ptr sp value address globalAddress mem globalType mapped global
    ?_ 9 (outputBytes mem.bytes ptr value) ?_
  · change 2 ^ 56 ≤ joinHalves (value.toBitVec.setWidth 32) ((value.toBitVec >>> 32).setWidth 32) ∧
      Bounds mem.bytes ptr
    rw [joinSplit, UInt64.toNat_toBitVec]
    exact ⟨wide, bounds⟩
  · intro final word stack observed
    change word = 9 ∧ stack = sp ∧
      final = outputBytes mem.bytes ptr
        (UInt64.ofNat (joinHalves (value.toBitVec.setWidth 32) ((value.toBitVec >>> 32).setWidth 32)))
      at observed
    rwa [joinSplit, UInt64.toNat_toBitVec, UInt64.ofNat_toNat] at observed

/-- Calling the reactor wrapper for any nine-byte input returns i32 9 and modifies
only the nine output bytes. The callee's i32 stack global is read in the common
prologue. The path needs no scratch-space premise. -/
theorem putVarint_nineByte {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {putFn : Func} {putAddress helperAddress : Nat}
    {putInstance helperInstance : FuncInst H} {ptr sp : BitVec 32} {value : UInt64}
    {address globalAddress : Nat} {mem : MemInst} {globalType : CGlobalType}
    (selected : definedFunction? sqlite 530 = some putFn)
    (putBinding : s.func? caller ⟨530⟩ = some (putAddress, putInstance))
    (helperBinding : s.func? (callFrame putInstance.module putFn ptr value) ⟨547⟩ =
      some (helperAddress, helperInstance))
    (putCode : putInstance.code = .wasm putFn)
    (helperCode : helperInstance.code = .wasm quotedHelper)
    (putType : Expand putInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (helperType : Expand helperInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (wide : 2 ^ 56 ≤ value.toNat)
    (mapped : s.mem? (callFrame helperInstance.module quotedHelper ptr value) ⟨0⟩ =
      some (address, mem))
    (global : s.global? (callFrame helperInstance.module quotedHelper ptr value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 sp⟩))
    (bounds : Bounds mem.bytes ptr) :
    Steps P host ⟨s, caller, vals (args ptr value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨s.setMem address { mem with bytes := outputBytes mem.bytes ptr value }, caller, [constI32 9]⟩ :=
  putVarint_forward selected putBinding helperBinding putCode helperCode putType helperType
    ((show 16384 ≤ 2 ^ 56 by decide).trans wide)
    (helper_nineByte s (callFrame putInstance.module putFn ptr value) helperInstance.module ptr sp
      value address globalAddress mem globalType wide mapped global bounds)

#print axioms helper_nineByte
#print axioms putVarint_nineByte

end SqliteWasm.NineByteVarint
