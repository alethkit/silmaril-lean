module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties
import SqliteWasm.GetVarintReaderSupport
import Silmaril.Wasm.Auto2.VCGen.Thms
import Silmaril.Wasm.Logic.Memory.Thms
import Silmaril.Wasm.Verify.Kernel.Defs



public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

open Silmaril.Wasm.Auto2.VCGen

open SqliteWasm.GetVarintReaderSupport
open Silmaril.Wasm.Logic.Core (bytesAt getElem?_bytesAt leNat_cons load_eq)

private theorem loadUnsignedByte (B : ByteArray) (index : Nat) (byte : UInt8)
    (input : B[index]? = some byte) : ldW 64 1 .unsigned B index = byte.toBitVec.setWidth 64 := by
  have bound := (getElem?_eq_some_iff.mp input).choose
  have pick : B.data.toList[index]? = some byte := by
    rw [getElem?_pos B index bound] at input
    simpa [ByteArray.getElem_eq_getElem_data, getElem?_pos B.data index
      (show index < B.data.size from bound)] using input
  have contents : bytesAt B ⟨index, 1⟩ = [byte] := by
    apply List.ext_getElem?
    intro i
    cases i <;> simp [getElem?_bytesAt, pick]
  unfold ldW rd
  rw [load_eq (by omega), contents, leNat_cons]
  change (BitVec.ofNat 8 byte.toBitVec.toNat).setWidth 64 = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private def nineByteValue (first second third fourth fifth sixth seventh eighth ninth : UInt8) : Nat :=
  (((((((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 +
    fourth.toNat % 128) * 128 + fifth.toNat % 128) * 128 + sixth.toNat % 128) * 128 +
    seventh.toNat % 128) * 128 + eighth.toNat % 128) * 256 + ninth.toNat

private structure NineByteInput (B : ByteArray) (src : BitVec 32)
    (first second third fourth fifth sixth seventh eighth ninth : UInt8) : Prop where
  firstByte : B[src.toNat]? = some first
  secondByte : B[src.toNat + 1]? = some second
  thirdByte : B[src.toNat + 2]? = some third
  fourthByte : B[src.toNat + 3]? = some fourth
  fifthByte : B[src.toNat + 4]? = some fifth
  sixthByte : B[src.toNat + 5]? = some sixth
  seventhByte : B[src.toNat + 6]? = some seventh
  eighthByte : B[src.toNat + 7]? = some eighth
  ninthByte : B[src.toNat + 8]? = some ninth
  firstContinues : 128 ≤ first.toNat
  secondContinues : 128 ≤ second.toNat
  thirdContinues : 128 ≤ third.toNat
  fourthContinues : 128 ≤ fourth.toNat
  fifthContinues : 128 ≤ fifth.toNat
  sixthContinues : 128 ≤ sixth.toNat
  seventhContinues : 128 ≤ seventh.toNat
  eighthContinues : 128 ≤ eighth.toNat

private theorem readNineByte (B : ByteArray) (src : BitVec 32)
    (first second third fourth fifth sixth seventh eighth ninth : UInt8)
    (input : NineByteInput B src first second third fourth fifth sixth seventh eighth ninth) :
    Varint.read? (File.View.ofBytes ⟨B⟩) src.toNat =
      some (UInt64.ofNat (nineByteValue first second third fourth fifth sixth seventh eighth ninth), src.toNat + 9) := by
  have firstContinues := Nat.not_lt.mpr input.firstContinues
  have secondContinues := Nat.not_lt.mpr input.secondContinues
  have thirdContinues := Nat.not_lt.mpr input.thirdContinues
  have fourthContinues := Nat.not_lt.mpr input.fourthContinues
  have fifthContinues := Nat.not_lt.mpr input.fifthContinues
  have sixthContinues := Nat.not_lt.mpr input.sixthContinues
  have seventhContinues := Nat.not_lt.mpr input.seventhContinues
  have eighthContinues := Nat.not_lt.mpr input.eighthContinues
  simp [Varint.read?, Varint.readNat?, Varint.readAux?, viewByte _ _ _ input.firstByte,
    viewByte _ _ _ input.secondByte, viewByte _ _ _ input.thirdByte, viewByte _ _ _ input.fourthByte,
    viewByte _ _ _ input.fifthByte, viewByte _ _ _ input.sixthByte, viewByte _ _ _ input.seventhByte,
    viewByte _ _ _ input.eighthByte, viewByte _ _ _ input.ninthByte,
    firstContinues, secondContinues,
    thirdContinues, fourthContinues, fifthContinues, sixthContinues, seventhContinues, eighthContinues,
     nineByteValue, Nat.add_assoc]

private abbrev reader := GetVarintReaderSupport.quoted

private def precondition (_ : Nat) (B : ByteArray) : List (BitVec 32) → Prop
  | [src, dst] => (∃ first second third fourth fifth sixth seventh eighth ninth,
      NineByteInput B src first second third fourth fifth sixth seventh eighth ninth) ∧ dst.toNat + 8 ≤ B.size
  | _ => False

private def postcondition (_ : Nat) (B final : ByteArray) : List (BitVec 32) → Prop
  | [src, dst] => ∃ first second third fourth fifth sixth seventh eighth ninth,
      NineByteInput B src first second third fourth fifth sixth seventh eighth ninth ∧
      final = Memory.writeSlice B dst.toNat
        (Memory.encodeLE 8 (nineByteValue first second third fourth fifth sixth seventh eighth ninth))
  | _ => False

private def model : Fns := { pr := precondition, pr2 := postcondition }

private abbrev spec := GetVarintReaderSupport.contract 9

private def generated : List Fm := genFunc spec reader 256

private theorem decodeWord (first second third fourth fifth sixth seventh eighth ninth : UInt8)
    (a : 128 ≤ first.toNat) (b : 128 ≤ second.toNat) (c : 128 ≤ third.toNat)
    (d : 128 ≤ fourth.toNat) (e : 128 ≤ fifth.toNat) (f : 128 ≤ sixth.toNat)
    (g : 128 ≤ seventh.toNat) (h : 128 ≤ eighth.toNat) :
    (finishWord (advanceWord (advanceWord (advanceWord (advanceWord (fourthWord (octetWord first) (octetWord second)
      (octetWord third) (octetWord fourth)) fifth) sixth) seventh) eighth) ninth).toNat =
         nineByteValue first second third fourth fifth sixth seventh eighth ninth := by
  obtain ⟨fits, pending⟩ := fifthPending first second third fourth fifth a b c d
  rw [pending, advancePending _ _ _ (by omega) e, advancePending _ _ _ (by omega) f,
    advancePending _ _ _ (by omega) g, finishPending _ _ _ (by omega) h]
  rfl

private theorem valid : AllValid model generated := by
  vcgen4_reduce
  vcgen4_den
  simp only [IntType.width, model, precondition, postcondition]
  and_intros
  all_goals vcgen4_vars
  all_goals intro h
  all_goals repeat' cases_type And
  all_goals subst_vars
  all_goals try assumption
  all_goals obtain ⟨first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, input⟩ :=
    (show ∃ a b c d e f g h i, NineByteInput M0 v0 a b c d e f g h i from by assumption)
  all_goals have firstLoad := loadByte _ _ _ input.firstByte
  all_goals have secondLoad := loadByte _ _ _ input.secondByte
  all_goals have thirdLoad := loadByte _ _ _ input.thirdByte
  all_goals have fourthLoad := loadByte _ _ _ input.fourthByte
  all_goals have fifthLoad := loadByte _ _ _ input.fifthByte
  all_goals have sixthLoad := loadByte _ _ _ input.sixthByte
  all_goals have seventhLoad := loadByte _ _ _ input.seventhByte
  all_goals have eighthLoad := loadByte _ _ _ input.eighthByte
  all_goals have ninthLoad := loadUnsignedByte _ _ _ input.ninthByte
  all_goals have firstContinues := signedContinues _ input.firstContinues
  all_goals have secondContinues := signedContinues _ input.secondContinues
  all_goals have thirdContinues := signedContinues _ input.thirdContinues
  all_goals have fourthContinues := signedContinues _ input.fourthContinues
  all_goals have fifthContinues := signedContinues _ input.fifthContinues
  all_goals have sixthContinues := signedContinues _ input.sixthContinues
  all_goals have seventhContinues := signedContinues _ input.seventhContinues
  all_goals have eighthContinues := signedContinues _ input.eighthContinues
  all_goals simp only [Nat.add_zero, firstLoad, secondLoad, thirdLoad, fourthLoad, fifthLoad,
    sixthLoad, seventhLoad, eighthLoad, ninthLoad, show (4294967295#32).toInt = -1 from rfl] at *
  all_goals try omega
  · have bound := (getElem?_eq_some_iff.mp input.firstByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.secondByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.thirdByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.fourthByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.fifthByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.sixthByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.seventhByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.eighthByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.ninthByte).choose
    omega
  · refine ⟨?_, first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, input, ?_⟩
    · rw [BitVec.add_comm v0 (8#32), BitVec.add_sub_cancel]
      rfl
    · rw [storeWord _ _ _ (by assumption)]
      change Memory.writeSlice _ _ (Memory.encodeLE 8
        (finishWord (advanceWord (advanceWord (advanceWord (advanceWord (fourthWord (octetWord first) (octetWord second)
          (octetWord third) (octetWord fourth)) fifth) sixth) seventh) eighth) ninth).toNat) = _
      rw [decodeWord first second third fourth fifth sixth seventh eighth ninth input.firstContinues
        input.secondContinues input.thirdContinues input.fourthContinues input.fifthContinues
        input.sixthContinues input.seventhContinues input.eighthContinues]

/-- The nine-byte branch of the pinned reactor reader, including overlong encodings.
All nine source lookups are on the initial callee memory. The eight-byte output may
overlap those bytes. The call returns i32 9 in the original caller frame. -/
theorem getVarint_nineByte {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {first second third fourth fifth sixth seventh eighth ninth : UInt8}
    {memoryAddr : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 434 = some fn)
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (firstByte : mem.bytes[src.toNat]? = some first)
    (secondByte : mem.bytes[src.toNat + 1]? = some second)
    (thirdByte : mem.bytes[src.toNat + 2]? = some third)
    (fourthByte : mem.bytes[src.toNat + 3]? = some fourth)
    (fifthByte : mem.bytes[src.toNat + 4]? = some fifth)
    (sixthByte : mem.bytes[src.toNat + 5]? = some sixth)
    (seventhByte : mem.bytes[src.toNat + 6]? = some seventh)
    (eighthByte : mem.bytes[src.toNat + 7]? = some eighth)
    (ninthByte : mem.bytes[src.toNat + 8]? = some ninth)
    (firstContinues : 128 ≤ first.toNat) (secondContinues : 128 ≤ second.toNat)
    (thirdContinues : 128 ≤ third.toNat) (fourthContinues : 128 ≤ fourth.toNat)
    (fifthContinues : 128 ≤ fifth.toNat) (sixthContinues : 128 ≤ sixth.toNat)
    (seventhContinues : 128 ≤ seventh.toNat) (eighthContinues : 128 ≤ eighth.toNat)
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    let value := (((((((first.toNat % 128 * 128 + second.toNat % 128) * 128 + third.toNat % 128) * 128 +
      fourth.toNat % 128) * 128 + fifth.toNat % 128) * 128 + sixth.toNat % 128) * 128 +
      seventh.toNat % 128) * 128 + eighth.toNat % 128) * 256 + ninth.toNat
    Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat =
        some (UInt64.ofNat value, src.toNat + 9) ∧
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 value) },
        caller, [constI32 9]⟩ := by
  have same := Option.some.inj (selected.symm.trans GetVarintReaderSupport.quotedSelected)
  subst fn
  have input : NineByteInput mem.bytes src first second third fourth fifth sixth seventh eighth ninth :=
    ⟨firstByte, secondByte, thirdByte, fourthByte, fifthByte, sixthByte, seventhByte, eighthByte, ninthByte,
      firstContinues, secondContinues, thirdContinues, fourthContinues, fifthContinues, sixthContinues,
      seventhContinues, eighthContinues⟩
  refine ⟨readNineByte _ _ _ _ _ _ _ _ _ _ _ input, ?_⟩
  refine GetVarintReaderSupport.call_of_vcs model 9 _ valid slot instanceAt code signature mapped
    ⟨⟨first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, input⟩, inBounds⟩ ?_
  intro bytes observed
  obtain ⟨a, b, c, d, e, f, g, h, i, observedInput, memory⟩ := observed
  obtain rfl : a = first := Option.some.inj (observedInput.firstByte.symm.trans input.firstByte)
  obtain rfl : b = second := Option.some.inj (observedInput.secondByte.symm.trans input.secondByte)
  obtain rfl : c = third := Option.some.inj (observedInput.thirdByte.symm.trans input.thirdByte)
  obtain rfl : d = fourth := Option.some.inj (observedInput.fourthByte.symm.trans input.fourthByte)
  obtain rfl : e = fifth := Option.some.inj (observedInput.fifthByte.symm.trans input.fifthByte)
  obtain rfl : f = sixth := Option.some.inj (observedInput.sixthByte.symm.trans input.sixthByte)
  obtain rfl : g = seventh := Option.some.inj (observedInput.seventhByte.symm.trans input.seventhByte)
  obtain rfl : h = eighth := Option.some.inj (observedInput.eighthByte.symm.trans input.eighthByte)
  obtain rfl : i = ninth := Option.some.inj (observedInput.ninthByte.symm.trans input.ninthByte)
  exact memory

#print axioms getVarint_nineByte

end SqliteWasm
