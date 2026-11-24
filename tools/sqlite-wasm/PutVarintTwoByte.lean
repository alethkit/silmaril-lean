module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties

public section

namespace SqliteWasm

set_option maxRecDepth 65536

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (Expand Ty)
open SqliteWasmArtifact

theorem encode_two (value : UInt64) (lower : 128 ≤ value.toNat)
    (upper : value.toNat < 16384) :
    Varint.encode value =
      Silmaril.Formats.Bytes.ofList [UInt8.ofNat (value.toNat / 128 + 128), UInt8.ofNat (value.toNat % 128)] := by
  have wide : value.toNat < 2 ^ 56 := by omega
  have divided : value.toNat / 128 < 128 := by omega
  unfold Varint.encode
  dsimp only
  rw [ite_eq_left wide]
  simp [Varint.seven, Nat.not_lt.mpr lower, divided, UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (show value.toNat / 128 < 256 by omega),
    Nat.mod_eq_of_lt divided, Nat.add_mod]

private theorem lowBits (value : UInt64) (upper : value.toNat < 16384) :
    (value.toBitVec.setWidth 32 &&& 127#32).toNat = value.toNat % 128 := by
  have fits : value.toNat < 2 ^ 32 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, UInt64.toNat_toBitVec,
    Nat.mod_eq_of_lt fits]
  exact Nat.and_two_pow_sub_one_eq_mod value.toNat 7

private theorem highBits (value : UInt64) (upper : value.toNat < 16384) :
    ((value.toBitVec.setWidth 32 >>> (7 : Nat)) ||| 128#32).toNat = value.toNat / 128 + 128 := by
  have fits : value.toNat < 2 ^ 32 := by omega
  have divided : value.toNat / 128 < 128 := by omega
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, UInt64.toNat_toBitVec,
    Nat.mod_eq_of_lt fits, Nat.shiftRight_eq_div_pow]
  exact Nat.or_two_pow_eq_add_of_lt (n := 7) divided

private theorem adjacentSplices {α : Type} (bytes : List α) (start : Nat) (first second : α)
    (bound : start + 2 ≤ bytes.length) :
    Memory.spliceL (Memory.spliceL bytes (start + 1) [second]) start [first] =
      Memory.spliceL bytes start [first, second] := by
  induction start generalizing bytes with
  | zero =>
    cases bytes with
    | nil => simp at bound
    | cons byte bytes =>
      cases bytes with
      | nil => simp at bound
      | cons next bytes => rfl
  | succ start ih =>
    cases bytes with
    | nil => simp at bound
    | cons byte bytes =>
      simpa only [Memory.spliceL, List.cons.injEq, true_and] using
        congrArg (List.cons byte) (ih bytes (by simp at bound; omega))

private def compareAndBranch (limit : BitVec 64) : List Instr :=
  [.localGet ⟨1⟩, .intConst .i64 limit, .intRelOp .i64 (.gt .unsigned), .brIf ⟨0⟩]

private def oneByteBody : List Instr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i64 (some .i8) ⟨0⟩ memarg0,
    .intConst .i32 1, .return_]

private def twoByteBody : List Instr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .convert .wrap, .localTee ⟨2⟩,
    .intConst .i32 127, .intBinOp .i32 .and, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 1⟩,
    .localGet ⟨0⟩, .localGet ⟨2⟩, .intConst .i32 7, .intBinOp .i32 (.shr .unsigned),
    .intConst .i32 128, .intBinOp .i32 .or, .intStore .i32 (some .i8) ⟨0⟩ memarg0,
    .intConst .i32 2, .return_]

private theorem guardSteps {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (s : Store H) (f : Frame) (value : UInt64) (limit : BitVec 64) (rest : List Instr)
    (localValue : f.local? ⟨1⟩ = some (some (.i64 value.toBitVec))) :
    Steps P host ⟨s, f, expression (compareAndBranch limit ++ rest)⟩
      ⟨s, f, if limit.toNat < value.toNat then .plain (.br ⟨0⟩) :: expression rest
        else expression rest⟩ := by
  have read : Step P host ⟨s, f, [.plain (.localGet ⟨1⟩)]⟩
      ⟨s, f, [.plain (.intConst .i64 value.toBitVec)]⟩ := .variable (.localGet (v := .i64 value.toBitVec) localValue)
  have compare : Step P host
      ⟨s, f, [.plain (.intConst .i64 value.toBitVec), .plain (.intConst .i64 limit),
        .plain (.intRelOp .i64 (.gt .unsigned))]⟩
      ⟨s, f, [constI32 (if limit.toNat < value.toNat then 1 else 0)]⟩ := by
    simpa [Numerics.intRelOp, Numerics.bool32, IntType.width, UInt64.toNat_toBitVec] using
      (Step.numeric (s := s) (f := f) (P := P) (host := host)
        (NumericStep.intRelOp (t := .i64) (op := .gt .unsigned) (x := value.toBitVec) (y := limit)))
  have test : Steps P host ⟨s, f, expression (compareAndBranch limit ++ rest)⟩
      ⟨s, f, [constI32 (if limit.toNat < value.toNat then 1 else 0), .plain (.brIf ⟨0⟩)]
        ++ expression rest⟩ :=
    (read.steps.ctxtInstrs (vs := []) (rest := [.plain (.intConst .i64 limit),
      .plain (.intRelOp .i64 (.gt .unsigned)), .plain (.brIf ⟨0⟩)] ++ expression rest)).trans
      (compare.steps.ctxtInstrs (vs := []) (rest := .plain (.brIf ⟨0⟩) :: expression rest))
  by_cases jump : limit.toNat < value.toNat
  · have branch : Step P host ⟨s, f, [constI32 1, .plain (.brIf ⟨0⟩)]⟩
        ⟨s, f, [.plain (.br ⟨0⟩)]⟩ := Step.brIfTrue (by decide)
    simp only [ite_eq_left jump] at test ⊢
    exact test.trans (branch.steps.ctxtInstrs (vs := []) (rest := expression rest))
  · have branch : Step P host ⟨s, f, [constI32 0, .plain (.brIf ⟨0⟩)]⟩
        ⟨s, f, []⟩ := Step.brIfFalse
    simp only [ite_eq_right jump] at test ⊢
    exact test.trans (branch.steps.ctxtInstrs (vs := []) (rest := expression rest))

private theorem packedStore {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {ptr word : BitVec 32} {arg : MemArg}
    {address : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (inBounds : effAddr ptr.toNat arg + 1 ≤ mem.bytes.size) (fits : word.toNat < 256) :
    Step P host ⟨s, f, [constI32 ptr, constI32 word, .plain (.intStore .i32 (some .i8) ⟨0⟩ arg)]⟩
      ⟨s.setMem address { mem with
        bytes := Memory.writeSlice mem.bytes (effAddr ptr.toNat arg) ⟨#[UInt8.ofNat word.toNat]⟩ }, f, []⟩ := by
  apply Step.memory
  apply MemoryStep.storePackVal (a := .i32) mapped
  change Memory.store mem.bytes (effAddr ptr.toNat arg) (count := 1) (word.setWidth 8) = _
  rw [Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left inBounds]
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits]
  rfl

private theorem mappedAfterStore {H : Type} {s : Store H} {f : Frame} {address : Nat}
    {mem : MemInst} (mapped : s.mem? f ⟨0⟩ = some (address, mem)) (newMem : MemInst) :
    (s.setMem address newMem).mem? f ⟨0⟩ = some (address, newMem) := by
  unfold Store.mem? at mapped ⊢
  obtain ⟨cell, slot, found⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨old, lookup, same⟩ := Option.bind_eq_some_iff.mp found
  rcases Prod.mk.inj (Option.some.inj same) with ⟨rfl, rfl⟩
  simp [slot, Store.setMem, List.getElem?_set_self', lookup]

private def putFrame (callee : ModuleInst) (ptr : BitVec 32) (value : UInt64) : Frame :=
  Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] [.i32]

private theorem executeTwoByteBody {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (ptr : BitVec 32) (value : UInt64) (address : Nat)
    (mem : MemInst) (lower : 128 ≤ value.toNat) (upper : value.toNat < 16384)
    (mapped : s.mem? (putFrame callee ptr value) ⟨0⟩ = some (address, mem))
    (inBounds : ptr.toNat + 2 ≤ mem.bytes.size) :
    let f := putFrame callee ptr value
    let f' := f.setLocal ⟨2⟩ (.i32 (value.toBitVec.setWidth 32))
    let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
    Steps P host ⟨s, f, expression twoByteBody⟩
      ⟨s.setMem address { mem with bytes := out }, f', [constI32 2, .plain .return_]⟩ := by
  dsimp only
  let f := putFrame callee ptr value
  let wrapped := value.toBitVec.setWidth 32
  let f' := f.setLocal ⟨2⟩ (.i32 wrapped)
  let trailing := wrapped &&& 127#32
  let shifted := wrapped >>> (7 : Nat)
  let leading := shifted ||| 128#32
  let trailingByte := UInt8.ofNat (value.toNat % 128)
  let leadingByte := UInt8.ofNat (value.toNat / 128 + 128)
  let afterTrailing : MemInst :=
    { mem with bytes := Memory.writeSlice mem.bytes (ptr.toNat + 1) ⟨#[trailingByte]⟩ }
  let s' := s.setMem address afterTrailing
  let finalMem : MemInst :=
    { mem with bytes := Memory.writeSlice afterTrailing.bytes ptr.toNat ⟨#[leadingByte]⟩ }
  have getPtr : Step P host ⟨s, f, [.plain (.localGet ⟨0⟩)]⟩ ⟨s, f, [constI32 ptr]⟩ :=
    .variable (.localGet rfl)
  have getValue : Step P host ⟨s, f, [.plain (.localGet ⟨1⟩)]⟩
      ⟨s, f, [.plain (.intConst .i64 value.toBitVec)]⟩ := .variable (.localGet (v := .i64 value.toBitVec) rfl)
  have wrap : Step P host ⟨s, f, [.plain (.intConst .i64 value.toBitVec), .plain (.convert .wrap)]⟩
      ⟨s, f, [constI32 wrapped]⟩ := by
    have converted : Numerics.convertP P .wrap value.toBitVec (.ok wrapped) := by
      unfold Numerics.convertP
      split <;> rfl
    exact .numeric (.convert converted)
  have tee : Step P host ⟨s, f, [constI32 wrapped, .plain (.localTee ⟨2⟩)]⟩
      ⟨s, f, [constI32 wrapped, constI32 wrapped, .plain (.localSet ⟨2⟩)]⟩ :=
    .variable (.localTee (v := .i32 wrapped))
  have setLocal : Step P host ⟨s, f, [constI32 wrapped, .plain (.localSet ⟨2⟩)]⟩
      ⟨s, f', []⟩ := .variable (.localSet (v := .i32 wrapped) (by change 2 < 3; decide))
  have mask : Step P host ⟨s, f', [constI32 wrapped, constI32 127, .plain (.intBinOp .i32 .and)]⟩
      ⟨s, f', [constI32 trailing]⟩ := .numeric (.intBinOp rfl)
  have trailingNat : trailing.toNat = value.toNat % 128 := lowBits value upper
  have trailingStore : Step P host
      ⟨s, f', [constI32 ptr, constI32 trailing, .plain (.intStore .i32 (some .i8) ⟨0⟩ ⟨0, 1⟩)]⟩
      ⟨s', f', []⟩ := by
    have step := packedStore (P := P) (host := host) (word := trailing) (arg := ⟨0, 1⟩)
      (show s.mem? f' ⟨0⟩ = some (address, mem) from mapped)
      (ptr := ptr) (by simpa [effAddr, Nat.add_assoc] using inBounds) (by omega)
    rw [trailingNat, show effAddr ptr.toNat (⟨0, 1⟩ : MemArg) = ptr.toNat + 1 from rfl] at step
    exact step
  have getPtr' : Step P host ⟨s', f', [.plain (.localGet ⟨0⟩)]⟩ ⟨s', f', [constI32 ptr]⟩ :=
    .variable (.localGet rfl)
  have getWrapped : Step P host ⟨s', f', [.plain (.localGet ⟨2⟩)]⟩ ⟨s', f', [constI32 wrapped]⟩ :=
    .variable (.localGet rfl)
  have shift : Step P host
      ⟨s', f', [constI32 wrapped, constI32 7, .plain (.intBinOp .i32 (.shr .unsigned))]⟩
      ⟨s', f', [constI32 shifted]⟩ := .numeric (.intBinOp rfl)
  have setContinuation : Step P host
      ⟨s', f', [constI32 shifted, constI32 128, .plain (.intBinOp .i32 .or)]⟩
      ⟨s', f', [constI32 leading]⟩ := .numeric (.intBinOp rfl)
  have afterSize : afterTrailing.bytes.size = mem.bytes.size := by
    apply Memory.writeBytes_size mem.bytes ⟨#[trailingByte]⟩ (start := ptr.toNat + 1)
    unfold Memory.writeBytes
    rw [show (⟨#[trailingByte]⟩ : ByteArray).size = 1 from rfl]
    exact ite_eq_left (by omega)
  have leadingNat : leading.toNat = value.toNat / 128 + 128 := highBits value upper
  have leadingStore : Step P host
      ⟨s', f', [constI32 ptr, constI32 leading, .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0)]⟩
      ⟨s'.setMem address finalMem, f', []⟩ := by
    have afterMapped : s'.mem? f' ⟨0⟩ = some (address, afterTrailing) :=
      mappedAfterStore (show s.mem? f' ⟨0⟩ = some (address, mem) from mapped) afterTrailing
    have step := packedStore (P := P) (host := host) (word := leading) (arg := memarg0)
      afterMapped (ptr := ptr) (by simp [effAddr, memarg0, afterSize]; omega) (by omega)
    rw [leadingNat, show effAddr ptr.toNat memarg0 = ptr.toNat from Nat.add_zero _] at step
    exact step
  have finalBytes : finalMem.bytes = Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data := by
    rw [encode_two value lower upper]
    exact congrArg (fun bytes => ByteArray.mk (Array.mk bytes))
      (adjacentSplices mem.bytes.data.toList ptr.toNat leadingByte trailingByte inBounds)
  have finalStore :
      s'.setMem address finalMem =
        s.setMem address { mem with bytes := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data } := by
    calc
      s'.setMem address finalMem = s.setMem address finalMem := by
        simp only [s', Store.setMem, List.set_set]
      _ = _ := congrArg (fun bytes => s.setMem address { mem with bytes := bytes }) finalBytes
  rw [← finalStore]
  simp only [twoByteBody, expression, List.map_cons, List.map_nil]
  refine (getPtr.steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (getValue.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  refine (wrap.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  refine (tee.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  refine (setLocal.steps.ctxtInstrs (vs := [.i32 ptr, .i32 wrapped]) (rest := _)).trans ?_
  refine (mask.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  refine (trailingStore.steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (getPtr'.steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (getWrapped.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  refine (shift.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  refine (setContinuation.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := _)).trans ?_
  exact leadingStore.steps.ctxtInstrs (vs := []) (rest := [constI32 2, .plain .return_])

private def firstBlock : List Instr := compareAndBranch 127 ++ oneByteBody
private def secondBlock : List Instr := compareAndBranch 16383 ++ twoByteBody

private theorem quotedTwoBytePrefix :
    (definedFunction? sqlite 530).map
      (fun fn => (fn.locals, fn.body.take 2)) =
    some ([.i32], [.block .empty firstBlock, .block .empty secondBlock]) := rfl

private theorem executeTwoByteCallFrame {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    (s : Store H) (caller : Frame) (callee : ModuleInst) (rest : List Instr)
    (ptr : BitVec 32) (value : UInt64) (address : Nat) (mem : MemInst)
    (lower : 128 ≤ value.toNat) (upper : value.toNat < 16384)
    (mapped : s.mem? (putFrame callee ptr value) ⟨0⟩ = some (address, mem))
    (inBounds : ptr.toNat + 2 ≤ mem.bytes.size) :
    let f := putFrame callee ptr value
    let body := .block .empty firstBlock :: .block .empty secondBlock :: rest
    let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
    Steps P host ⟨s, caller, [.frame 1 f [.label 1 [] (expression body)]]⟩
      ⟨s.setMem address { mem with bytes := out }, caller,
        [constI32 (BitVec.ofNat 32 (Varint.encode value).length)]⟩ := by
  dsimp only
  let f := putFrame callee ptr value
  let f' := f.setLocal ⟨2⟩ (.i32 (value.toBitVec.setWidth 32))
  let t := s.setMem address { mem with bytes := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data }
  let returned := [constI32 2, Admin.plain .return_]
  have enter (code : List Instr) :
      Step P host ⟨s, f, [.plain (.block .empty code)]⟩
        ⟨s, f, [.label 0 [] (expression code)]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have skipFirst : (127 : BitVec 64).toNat < value.toNat := by
    change 127 < value.toNat
    omega
  have firstGuard : Steps P host ⟨s, f, expression firstBlock⟩
      ⟨s, f, .plain (.br ⟨0⟩) :: expression oneByteBody⟩ := by
    simpa only [firstBlock, ite_eq_left skipFirst] using
      (guardSteps (P := P) (host := host) s f value 127 oneByteBody rfl)
  have exitFirst : Step P host
      ⟨s, f, [.label 0 [] (.plain (.br ⟨0⟩) :: expression oneByteBody)]⟩ ⟨s, f, []⟩ :=
    Step.brLabelZero (vs' := []) (vs := []) (rest := expression oneByteBody) rfl rfl
  have firstDone : Steps P host ⟨s, f, [.plain (.block .empty firstBlock)]⟩ ⟨s, f, []⟩ :=
    ((enter firstBlock).steps.trans (firstGuard.label (n := 0) (cont := []))).tail exitFirst
  have takeSecond : ¬ (16383 : BitVec 64).toNat < value.toNat := by
    change ¬ 16383 < value.toNat
    omega
  have secondGuard : Steps P host ⟨s, f, expression secondBlock⟩ ⟨s, f, expression twoByteBody⟩ := by
    simpa only [secondBlock, ite_eq_right takeSecond] using
      (guardSteps (P := P) (host := host) s f value 16383 twoByteBody rfl)
  have secondBody : Steps P host ⟨s, f, expression secondBlock⟩ ⟨t, f', returned⟩ :=
    secondGuard.trans (executeTwoByteBody s callee ptr value address mem lower upper mapped inBounds)
  have exitLabel (arity : Nat) (suffix : List Admin) :
      Step P host ⟨t, f', [.label arity [] (returned ++ suffix)]⟩ ⟨t, f', returned⟩ :=
    Step.returnLabel (vs := [.i32 2])
  have secondDone : Steps P host ⟨s, f, [.plain (.block .empty secondBlock)]⟩ ⟨t, f', returned⟩ :=
    ((enter secondBlock).steps.trans (secondBody.label (n := 0) (cont := []))).tail (exitLabel 0 [])
  have withRest : Steps P host
      ⟨s, f, expression (.block .empty firstBlock :: .block .empty secondBlock :: rest)⟩
      ⟨t, f', returned ++ expression rest⟩ :=
    (firstDone.ctxtInstrs (vs := []) (rest := .plain (.block .empty secondBlock) :: expression rest)).trans
      (secondDone.ctxtInstrs (vs := []) (rest := expression rest))
  have inside := (withRest.label (n := 1) (cont := [])).tail (exitLabel 1 (expression rest))
  have exitFrame : Step P host ⟨t, caller, [.frame 1 f' returned]⟩ ⟨t, caller, [constI32 2]⟩ :=
    Step.returnFrame (vs' := []) (vs := [.i32 2]) (rest := []) rfl
  have width : (Varint.encode value).length = 2 := by simp [encode_two value lower upper]
  rw [width]
  exact (Steps.frame (f := caller) (n := 1) inside).tail exitFrame

/-- A call to the quoted reactor function 530 for an unsigned value in `[128, 16384)`.
With the stated function binding and two in-bounds bytes, the call restores the caller frame,
writes the Lean encoding at the supplied i32 address and returns its length. -/
theorem putVarint_twoByte {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {ptr : BitVec 32} {value : UInt64} {memoryAddr : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 530 = some fn)
    (slot : caller.module.funcs[530]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (lower : 128 ≤ value.toNat) (upper : value.toNat < 16384)
    (mapped : s.mem? (Frame.forCall fi.module [.i32 ptr, .i64 value.toBitVec] fn.locals) ⟨0⟩ =
      some (memoryAddr, mem))
    (inBounds : ptr.toNat + 2 ≤ mem.bytes.size) :
    let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
    Steps P host ⟨s, caller, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)]⟩
      ⟨s.setMem memoryAddr { mem with bytes := out }, caller,
        [constI32 (BitVec.ofNat 32 (Varint.encode value).length)]⟩ := by
  have quoted := quotedTwoBytePrefix
  rw [selected] at quoted
  have shape := Option.some.inj quoted
  have locals : fn.locals = [.i32] := congrArg Prod.fst shape
  have body : fn.body = .block .empty firstBlock :: .block .empty secondBlock :: fn.body.drop 2 :=
    (List.take_append_drop 2 fn.body).symm.trans (congrArg (· ++ fn.body.drop 2) (congrArg Prod.snd shape))
  have enters := (Step.call (P := P) (host := host) (x := (⟨530⟩ : FuncIdx)) slot instanceAt).steps
  refine (enters.ctxtInstrs (vs := [.i32 ptr, .i64 value.toBitVec]) (rest := [])).trans ?_
  refine Relation.ReflTransGen.head
    (Step.callRefFunc (c := .callRefType fi.type) (vs := [.i32 ptr, .i64 value.toBitVec])
      trivial instanceAt signature rfl code) ?_
  rw [locals, body]
  rw [locals] at mapped
  exact executeTwoByteCallFrame s caller fi.module (fn.body.drop 2) ptr value memoryAddr mem
    lower upper mapped inBounds

#print axioms putVarint_twoByte

end SqliteWasm
