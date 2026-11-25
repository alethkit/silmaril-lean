module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties
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

private def twoByteValue (first second : UInt8) : Nat :=
  first.toNat % 128 * 128 + second.toNat

private structure TwoByteInput (B : ByteArray) (src : BitVec 32) (first second : UInt8) : Prop where
  firstByte : B[src.toNat]? = some first
  secondByte : B[src.toNat + 1]? = some second
  continues : 128 ≤ first.toNat
  ends : second.toNat < 128

private theorem viewByte (B : ByteArray) (index : Nat) (byte : UInt8)
    (input : B[index]? = some byte) :
    (File.View.ofBytes ⟨B⟩).get? index = some byte := by
  have bound := (getElem?_eq_some_iff.mp input).choose
  simpa [File.View.ofBytes, File.View.get?, Silmaril.Formats.Bytes.length, bound] using input

private theorem readTwoByte (B : ByteArray) (src : BitVec 32) (first second : UInt8)
    (input : TwoByteInput B src first second) :
    Varint.read? (File.View.ofBytes ⟨B⟩) src.toNat =
      some (UInt64.ofNat (twoByteValue first second), src.toNat + 2) := by
  have firstContinues := Nat.not_lt.mpr input.continues
  simp [Varint.read?, Varint.readNat?, Varint.readAux?,
    viewByte _ _ _ input.firstByte, viewByte _ _ _ input.secondByte,
    firstContinues, input.ends, Nat.mod_eq_of_lt input.ends, twoByteValue, Nat.add_assoc]

open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Core (bytesAt getElem?_bytesAt leNat_cons load_eq)

private def reader : Func := (definedFunction? sqlite 434).get (by kernel_rfl)

private def precondition (_ : Nat) (B : ByteArray) : List (BitVec 32) → Prop
  | [src, dst] => (∃ first second, TwoByteInput B src first second) ∧ dst.toNat + 8 ≤ B.size
  | _ => False

private def postcondition (_ : Nat) (B final : ByteArray) : List (BitVec 32) → Prop
  | [src, dst] => ∃ first second, TwoByteInput B src first second ∧
      final = Memory.writeSlice B dst.toNat (Memory.encodeLE 8 (twoByteValue first second))
  | _ => False

private def model : Fns := { pr := precondition, pr2 := postcondition }

private def spec : FnSpec :=
  { params := [.i32, .i32]
    results := [.i32]
    mem := true
    total := true
    pre := .pr 0 (.v 0) [.var .i32 0, .var .i32 1]
    post := .and (.rel .eq (.loc .i32 0) (.lit .i32 2))
      (.pr2 0 (.v 0) .cur [.var .i32 0, .var .i32 1]) }

private def generated : List Fm := genFunc spec reader 256

private theorem loadByte (B : ByteArray) (index : Nat) (byte : UInt8)
    (input : B[index]? = some byte) :
    ldW 32 1 .signed B index = byte.toBitVec.signExtend 32 := by
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
  change (BitVec.ofNat 8 byte.toBitVec.toNat).signExtend 32 = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem signedContinues (byte : UInt8) (high : 128 ≤ byte.toNat) :
    (byte.toBitVec.signExtend 32).toInt ≤ -1 := by
  have sign : byte.toBitVec.msb = true := BitVec.msb_eq_true_iff_two_mul_ge.mpr (by
    rw [UInt8.toNat_toBitVec]
    omega)
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_msb_cond, sign]
  have bound := byte.toNat_lt
  simp only [↓reduceIte, UInt8.toNat_toBitVec]
  omega

private theorem signedEnds (byte : UInt8) (low : byte.toNat < 128) :
    -1 < (byte.toBitVec.signExtend 32).toInt := by
  have sign : byte.toBitVec.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by
    rw [UInt8.toNat_toBitVec]
    omega)
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_of_msb sign]
  omega

private theorem maskByte (byte : UInt8) :
    ((byte.toBitVec.signExtend 32).setWidth 64 &&& 255#64).toNat = byte.toNat := by
  rw [BitVec.toNat_and]
  change ((byte.toBitVec.signExtend 32).setWidth 64).toNat &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth_of_le (by decide),
    BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide), UInt8.toNat_toBitVec]
  have bound := byte.toNat_lt
  cases byte.toBitVec.msb <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem shiftXor (x y : BitVec 64) (small : y.toNat < 128) :
    (x <<< 7 ^^^ y) = (x <<< 7) + y := by
  have disjoint (i : Nat) : ((x <<< 7).getLsbD i && y.getLsbD i) = false := by
    by_cases low : i < 7
    · simp [BitVec.getLsbD_shiftLeft, low]
    · have zero : y.getLsbD i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (show 0 < 2 by decide) (show 7 ≤ i by omega)))
      simp [zero]
  have mask : (x <<< 7) &&& y = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    change ((x <<< 7) &&& y).getLsbD i = (0#64).getLsbD i
    rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    exact disjoint i
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ mask]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have atBit := disjoint i
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or]
  cases hx : (x <<< 7).getLsbD i <;> cases hy : y.getLsbD i
  all_goals first | rfl | rw [hx, hy] at atBit; contradiction

private theorem decodeWord (first second : UInt8) (ends : second.toNat < 128) :
    ((((first.toBitVec.signExtend 32).setWidth 64 &&& 255#64) <<< 7 ^^^
      ((second.toBitVec.signExtend 32).setWidth 64 &&& 255#64)) &&& 16383#64).toNat =
      twoByteValue first second := by
  rw [shiftXor _ _ (by rw [maskByte]; exact ends), BitVec.toNat_and]
  change ((_ + _ : BitVec 64).toNat &&& (2 ^ 14 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    maskByte, maskByte, Nat.shiftLeft_eq]
  have bound := first.toNat_lt
  unfold twoByteValue
  omega

private theorem storeWord (B : ByteArray) (dst : BitVec 32) (word : BitVec 64)
    (bounds : dst.toNat + 8 ≤ B.size) :
    stW 64 8 B dst.toNat word = Memory.writeSlice B dst.toNat (Memory.encodeLE 8 word.toNat) := by
  rw [stW, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bounds]
  simp

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
  all_goals obtain ⟨first, second, input⟩ :=
    (show ∃ a b, TwoByteInput M0 v0 a b from by assumption)
  all_goals have firstLoad := loadByte _ _ _ input.firstByte
  all_goals have secondLoad := loadByte _ _ _ input.secondByte
  all_goals have continues := signedContinues _ input.continues
  all_goals have ends := signedEnds _ input.ends
  all_goals simp only [Nat.add_zero, firstLoad, secondLoad,
    show (4294967295#32).toInt = -1 from rfl] at *
  all_goals try omega
  · have bound := (getElem?_eq_some_iff.mp input.firstByte).choose
    omega
  · have bound := (getElem?_eq_some_iff.mp input.secondByte).choose
    omega
  · refine ⟨?_, first, second, input, ?_⟩
    · rw [BitVec.add_comm v0 (1#32), BitVec.add_sub_cancel]
      rfl
    · rw [storeWord _ _ _ (by assumption), decodeWord first second input.ends]

open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)

private theorem reachesResult {H : Type} {P : Profile} {host : HostSemantics H}
    {start : Config H} {store : Store H} {caller : Frame} {result : List Val}
    (safe : TSafe P host (fun s f o => s = store ∧ f = caller ∧ o = .normal result) start) :
    Steps P host start ⟨store, caller, vals result⟩ := by
  induction safe with
  | @exit c outcome exits post =>
    rcases c with ⟨before, frame, code⟩
    obtain ⟨rfl, rfl, rfl⟩ := post
    change code = vals result at exits
    subst code
    exact .refl
  | step progress _ ih =>
    obtain ⟨next, step⟩ := progress
    exact step.steps.trans (ih next step)

private theorem singleResult (results : List Val) (types : results.map valTy = [some .i32]) :
    ∃ word : BitVec 32, results = [.i32 word] := by
  cases results with
  | nil => simp at types
  | cons value rest =>
    obtain rfl : rest = [] := by simpa using congrArg List.length types
    rcases value with ⟨⟨t, word⟩⟩ | ⟨⟩ | ⟨⟩
    · rcases t with t | t
      · cases t
        · exact ⟨word, rfl⟩
        · simp [valTy] at types
      · simp [valTy] at types
    · simp [valTy] at types
    · simp [valTy] at types

private theorem runTwoByte {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {first second : UInt8} {memoryAddr : Nat} {mem : MemInst}
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm reader)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (input : TwoByteInput mem.bytes src first second)
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    let out := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 (twoByteValue first second))
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr { mem with bytes := out }, caller, [constI32 2]⟩ := by
  dsimp only
  unfold Store.mem? at mapped
  obtain ⟨ma, memLink, rest⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨mi, memEntry, pair⟩ := Option.bind_eq_some_iff.mp rest
  rcases Prod.mk.inj (Option.some.inj pair) with ⟨rfl, rfl⟩
  change fi.module.mems[0]? = some ma at memLink
  let ρ : Env := ⟨(fun i => if i = 0 then src else dst), (fun _ => 0), fun _ => mi.bytes⟩
  have hm : MemOk spec s fi.module (ρ.mem 0) := ⟨ma, mi, memLink, memEntry, rfl⟩
  have hg : GlobOk spec s fi.module ρ := by simp [GlobOk, spec]
  have pre : (fspec model spec instanceAddr fi).pre s [.i32 src, .i32 dst] :=
    ⟨instanceAt, by simp [Callees, spec], ρ, rfl, hm, hg, ⟨⟨first, second, input⟩, inBounds⟩⟩
  have total : TFSpecAt P host instanceAddr (fspec model spec instanceAddr fi) :=
    genFunc_tsound rfl code signature rfl rfl valid (by simp [CalleesValid, spec])
  let out := Memory.writeSlice mi.bytes dst.toNat (Memory.encodeLE 8 (twoByteValue first second))
  let Q : Post H := fun t f o => t = s.setMem ma { mi with bytes := out } ∧
    f = caller ∧ o = .normal [.i32 2]
  have safe : TSafe P host Q
      ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩ := by
    apply TSafe.callIdx (vs₀ := []) (rest := []) (x := ⟨434⟩) slot instanceAt total pre
    intro final outcome call
    rcases call.2 with ⟨results, rfl, post⟩ | ⟨rfl, post⟩ | ⟨tag, rfl, post⟩
    · obtain ⟨bytes, globals, store, globalTypes, result, same, _, types, facts⟩ := post
      cases same
      obtain rfl : globals = [] := by simpa [spec] using globalTypes
      obtain ⟨word, rfl⟩ := singleResult results types
      have observed := facts ρ rfl hm hg
      change word = 2 ∧ ∃ a b, TwoByteInput mi.bytes src a b ∧
        bytes = Memory.writeSlice mi.bytes dst.toNat (Memory.encodeLE 8 (twoByteValue a b))
        at observed
      obtain ⟨rfl, a, b, observedInput, rfl⟩ := observed
      obtain rfl : a = first := Option.some.inj (observedInput.firstByte.symm.trans input.firstByte)
      obtain rfl : b = second := Option.some.inj (observedInput.secondByte.symm.trans input.secondByte)
      rw [setGs_nil] at store
      change _ = setM s fi.module out at store
      rw [setM_some memLink memEntry] at store
      exact .exit (.normal [.i32 2]) rfl ⟨store, rfl, rfl⟩
    · obtain ⟨_, _, _, _, _, impossible, _⟩ := post
      cases impossible
    · obtain ⟨_, _, _, _, _, impossible, _⟩ := post
      cases impossible
  exact reachesResult safe

/-- The two-byte branch of the pinned reactor reader at slot 434. The first byte
continues and the second terminates, including overlong two-byte encodings.
Both byte lookups use the initial callee memory. The eight-byte destination may
overlap either input. The Core call returns i32 2 to the original caller frame. -/
theorem getVarint_twoByte {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {first second : UInt8} {memoryAddr : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 434 = some fn)
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (firstByte : mem.bytes[src.toNat]? = some first)
    (secondByte : mem.bytes[src.toNat + 1]? = some second)
    (continues : 128 ≤ first.toNat) (ends : second.toNat < 128)
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    let value := first.toNat % 128 * 128 + second.toNat
    Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat =
        some (UInt64.ofNat value, src.toNat + 2) ∧
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 value) },
        caller, [constI32 2]⟩ := by
  have linked : definedFunction? sqlite 434 = some reader := by kernel_rfl
  have same := Option.some.inj (selected.symm.trans linked)
  subst fn
  have input : TwoByteInput mem.bytes src first second := ⟨firstByte, secondByte, continues, ends⟩
  exact ⟨readTwoByte _ _ _ _ input, runTwoByte slot instanceAt code signature mapped input inBounds⟩

#print axioms getVarint_twoByte

end SqliteWasm
