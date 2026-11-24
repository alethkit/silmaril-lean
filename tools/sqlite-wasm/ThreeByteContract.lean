module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

namespace SqliteWasm.ThreeByte

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CGlobalType Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 65536

def scratchAddress (stackPointer : BitVec 32) : Nat := stackPointer.toNat - 10

/-- The nonwrapping, disjoint output and scratch ranges used by the three-byte path. -/
structure Buffers (bytes : ByteArray) (output stackPointer : BitVec 32) : Prop where
  stackSubtraction : 16 ≤ stackPointer.toNat
  outputNoWrap : output.toNat + 3 ≤ 2 ^ 32
  outputInBounds : output.toNat + 3 ≤ bytes.size
  scratchInBounds : scratchAddress stackPointer + 3 ≤ bytes.size
  disjoint : output.toNat + 3 ≤ scratchAddress stackPointer ∨
    scratchAddress stackPointer + 3 ≤ output.toNat

/-- The helper leaves the encoded digits in scratch in reverse byte order. -/
def scratchBytes (value : UInt64) : ByteArray :=
  ⟨⟨(Varint.encode value).toList.reverse⟩⟩

/-- The expected byte image after the helper's scratch writes and output copy. -/
def outputBytes (bytes : ByteArray) (output stackPointer : BitVec 32) (value : UInt64) : ByteArray :=
  Memory.writeSlice (Memory.writeSlice bytes (scratchAddress stackPointer) (scratchBytes value))
    output.toNat (Varint.encode value).data

def args (output : BitVec 32) (value : UInt64) : List Val := [.i32 output, .i64 value.toBitVec]

def callFrame (callee : ModuleInst) (fn : Func) (output : BitVec 32) (value : UInt64) : Frame :=
  Frame.forCall callee (args output value) fn.locals

def activation (callee : ModuleInst) (fn : Func) (output : BitVec 32) (value : UInt64) : Admin :=
  .frame 1 (callFrame callee fn output value) [.label 1 [] (expression fn.body)]

def postStore {H : Type} (s : Store H) (address : Nat) (mem : MemInst)
    (output stackPointer : BitVec 32) (value : UInt64) : Store H :=
  s.setMem address { mem with bytes := outputBytes mem.bytes output stackPointer value }

/-- One entered call to the quoted helper. Its result fixes the caller frame, width, and
both modified byte ranges in the store. -/
def HelperRun {H : Type} (P : Profile) (host : HostSemantics H)
    (s : Store H) (caller : Frame) (fn : Func) (callee : ModuleInst)
    (output stackPointer : BitVec 32) (value : UInt64) (address : Nat) (mem : MemInst) : Prop :=
  definedFunction? sqlite 547 = some fn ∧
  Steps P host ⟨s, caller, [activation callee fn output value]⟩
    ⟨postStore s address mem output stackPointer value, caller, [constI32 3]⟩

/-- The width-three callee obligation. Memory 0 and the i32 stack pointer in global 0
are resolved in the helper's own instance. -/
def HelperContract {H : Type} (P : Profile) (host : HostSemantics H)
    (fn : Func) (callee : ModuleInst) : Prop :=
  ∀ (s : Store H) (caller : Frame) (output stackPointer : BitVec 32) (value : UInt64)
    (address globalAddress : Nat) (mem : MemInst) (globalType : CGlobalType),
    16384 ≤ value.toNat → value.toNat < 2097152 →
    s.mem? (callFrame callee fn output value) ⟨0⟩ = some (address, mem) →
    s.global? (callFrame callee fn output value) ⟨0⟩ =
      some (globalAddress, ⟨globalType, .i32 stackPointer⟩) →
    Buffers mem.bytes output stackPointer →
    HelperRun P host s caller fn callee output stackPointer value address mem

theorem scratchAddress_eq (stackPointer : BitVec 32) (inFrame : 16 ≤ stackPointer.toNat) :
    (stackPointer - 16 + 6).toNat = scratchAddress stackPointer := by
  have sub : (stackPointer - 16).toNat = stackPointer.toNat - 16 :=
    BitVec.toNat_sub_of_le (by exact inFrame)
  have sum : (stackPointer - 16).toNat + (6 : BitVec 32).toNat < 2 ^ 32 := by
    rw [sub]
    have bound := stackPointer.isLt
    change stackPointer.toNat - 16 + 6 < 2 ^ 32
    omega
  rw [BitVec.toNat_add_of_lt sum, sub, scratchAddress]
  change stackPointer.toNat - 16 + 6 = stackPointer.toNat - 10
  omega

theorem encode_three (value : UInt64) (lower : 16384 ≤ value.toNat)
    (upper : value.toNat < 2097152) :
    Varint.encode value = Silmaril.Formats.Bytes.ofList
      [UInt8.ofNat (value.toNat / 16384 + 128), UInt8.ofNat (value.toNat / 128 % 128 + 128),
        UInt8.ofNat (value.toNat % 128)] := by
  have wide : value.toNat < 2 ^ 56 := by omega
  have more : ¬ value.toNat < 128 := by omega
  have divided : ¬ value.toNat / 128 < 128 := by omega
  have last : value.toNat / 16384 < 128 := by omega
  unfold Varint.encode
  dsimp only
  rw [ite_eq_left wide]
  simp [Varint.seven, more, divided, Nat.div_div_eq_div_mul, last,
    Nat.mod_eq_of_lt (show value.toNat / 16384 < 256 by omega), Nat.mod_eq_of_lt last,
    Nat.add_mod, UInt8.toNat_ofNat']

theorem scratchBytes_eq (value : UInt64) (lower : 16384 ≤ value.toNat)
    (upper : value.toNat < 2097152) :
    scratchBytes value =
      ⟨#[UInt8.ofNat (value.toNat % 128), UInt8.ofNat (value.toNat / 128 % 128 + 128),
        UInt8.ofNat (value.toNat / 16384 + 128)]⟩ := by
  rw [scratchBytes, encode_three value lower upper]
  rfl

private def compareAndBranch (limit : BitVec 64) : List Instr :=
  [.localGet ⟨1⟩, .intConst .i64 limit, .intRelOp .i64 (.gt .unsigned), .brIf ⟨0⟩]

private def remainingBlock (fn : Func) (index : Nat) : List Instr :=
  match fn.body[index]? with
  | some (.block .empty body) => body.drop 4
  | _ => []

private def forwardingBody (fn : Func) : List Instr :=
  [.block .empty (compareAndBranch 127 ++ remainingBlock fn 0),
    .block .empty (compareAndBranch 16383 ++ remainingBlock fn 1),
    .localGet ⟨0⟩, .localGet ⟨1⟩, .call ⟨547⟩]

private theorem actualForwarding {fn : Func} (selected : definedFunction? sqlite 530 = some fn) :
    fn.body = forwardingBody fn := by
  have checked : (definedFunction? sqlite 530).map Func.body =
      (definedFunction? sqlite 530).map forwardingBody := rfl
  rw [selected] at checked
  exact Option.some.inj checked

private theorem skipBlock {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (f : Frame) (value : UInt64) (limit : BitVec 64) (rest : List Instr)
    (readValue : f.local? ⟨1⟩ = some (some (.i64 value.toBitVec))) (above : limit.toNat < value.toNat) :
    Steps P host ⟨s, f, [.plain (.block .empty (compareAndBranch limit ++ rest))]⟩ ⟨s, f, []⟩ := by
  have enter : Step P host
      ⟨s, f, [.plain (.block .empty (compareAndBranch limit ++ rest))]⟩
      ⟨s, f, [.label 0 [] (expression (compareAndBranch limit ++ rest))]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have read : Step P host ⟨s, f, [.plain (.localGet ⟨1⟩)]⟩
      ⟨s, f, [.plain (.intConst .i64 value.toBitVec)]⟩ := .variable (.localGet (v := .i64 _) readValue)
  have compare : Step P host
      ⟨s, f, [.plain (.intConst .i64 value.toBitVec), .plain (.intConst .i64 limit),
        .plain (.intRelOp .i64 (.gt .unsigned))]⟩
      ⟨s, f, [constI32 1]⟩ := by
    simpa [Numerics.intRelOp, Numerics.bool32, IntType.width, UInt64.toNat_toBitVec, above] using
      (Step.numeric (s := s) (f := f) (P := P) (host := host)
        (NumericStep.intRelOp (t := .i64) (op := .gt .unsigned) (x := value.toBitVec) (y := limit)))
  have branch : Step P host ⟨s, f, [constI32 1, .plain (.brIf ⟨0⟩)]⟩
      ⟨s, f, [.plain (.br ⟨0⟩)]⟩ := Step.brIfTrue (by decide)
  have body : Steps P host ⟨s, f, expression (compareAndBranch limit ++ rest)⟩
      ⟨s, f, .plain (.br ⟨0⟩) :: expression rest⟩ := by
    refine (read.steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
    refine (compare.steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
    exact branch.steps.ctxtInstrs (vs := []) (rest := expression rest)
  have leave : Step P host ⟨s, f, [.label 0 [] (.plain (.br ⟨0⟩) :: expression rest)]⟩ ⟨s, f, []⟩ :=
    Step.brLabelZero (vs' := []) (vs := []) (rest := expression rest) rfl rfl
  exact (enter.steps.trans (body.label (n := 0) (cont := []))).tail leave

private theorem forwardArguments {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (fn : Func) (output : BitVec 32) (value : UInt64)
    (selected : definedFunction? sqlite 530 = some fn) (lower : 16384 ≤ value.toNat) :
    let f := callFrame callee fn output value
    Steps P host ⟨s, f, expression fn.body⟩
      ⟨s, f, vals (args output value) ++ [.plain (.call ⟨547⟩)]⟩ := by
  dsimp only
  let f := callFrame callee fn output value
  have firstBound : (127 : BitVec 64).toNat < value.toNat := by
    change 127 < value.toNat
    omega
  have secondBound : (16383 : BitVec 64).toNat < value.toNat := by
    change 16383 < value.toNat
    omega
  have first := skipBlock (P := P) (host := host) s f value 127 (remainingBlock fn 0) rfl firstBound
  have second := skipBlock (P := P) (host := host) s f value 16383 (remainingBlock fn 1) rfl secondBound
  have getOutput : Step P host ⟨s, f, [.plain (.localGet ⟨0⟩)]⟩ ⟨s, f, [constI32 output]⟩ :=
    .variable (.localGet (v := .i32 output) rfl)
  have getValue : Step P host ⟨s, f, [.plain (.localGet ⟨1⟩)]⟩
      ⟨s, f, [.plain (.intConst .i64 value.toBitVec)]⟩ :=
    .variable (.localGet (v := .i64 value.toBitVec) rfl)
  rw [actualForwarding selected]
  simp only [forwardingBody, expression, List.map_cons, List.map_nil]
  refine (first.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (second.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (getOutput.steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
  exact getValue.steps.ctxtInstrs (vs := [.i32 output]) (rest := [.plain (.call ⟨547⟩)])

private theorem enterCall {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {index : FuncIdx} {address : Nat} {fi : FuncInst H} {fn : Func}
    (output : BitVec 32) (value : UInt64)
    (bound : s.func? caller index = some (address, fi))
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil))) :
    Steps P host ⟨s, caller, vals (args output value) ++ [.plain (.call index)]⟩
      ⟨s, caller, [activation fi.module fn output value]⟩ := by
  unfold Store.func? at bound
  obtain ⟨slot, linked, found⟩ := Option.bind_eq_some_iff.mp bound
  obtain ⟨entry, lookup, equal⟩ := Option.bind_eq_some_iff.mp found
  rcases Prod.mk.inj (Option.some.inj equal) with ⟨rfl, rfl⟩
  have read := (Step.call (P := P) (host := host) linked lookup).steps
  refine (read.ctxtInstrs (vs := args output value) (rest := [])).tail ?_
  exact Step.callRefFunc (c := .callRefType _) (vs := args output value)
    trivial lookup signature rfl code

/-- The quoted wrapper forwards the original arguments to the quoted helper at slot 547.
Discharging the helper contract suffices for the three-byte call, including the scratch
side effects, the returned width and restoration of the caller frame. -/
theorem putVarint_threeByte_of_helper {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {putFn helperFn : Func}
    {putAddress helperAddress : Nat} {putInstance helperInstance : FuncInst H}
    {output stackPointer : BitVec 32} {value : UInt64} {address : Nat} {mem : MemInst}
    (selectedPut : definedFunction? sqlite 530 = some putFn)
    (putBinding : s.func? caller ⟨530⟩ = some (putAddress, putInstance))
    (helperBinding : s.func? (callFrame putInstance.module putFn output value) ⟨547⟩ =
      some (helperAddress, helperInstance))
    (putCode : putInstance.code = .wasm putFn)
    (helperCode : helperInstance.code = .wasm helperFn)
    (putType : Expand putInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (helperType : Expand helperInstance.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (lower : 16384 ≤ value.toNat)
    (helper : HelperRun P host s (callFrame putInstance.module putFn output value)
      helperFn helperInstance.module output stackPointer value address mem) :
    Steps P host ⟨s, caller, vals (args output value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨postStore s address mem output stackPointer value, caller, [constI32 3]⟩ := by
  let f := callFrame putInstance.module putFn output value
  let final := postStore s address mem output stackPointer value
  have enterPut := enterCall (P := P) (host := host) output value putBinding putCode putType
  have forward := forwardArguments (P := P) (host := host) s putInstance.module putFn output value
    selectedPut lower
  have enterHelper := enterCall (P := P) (host := host) output value helperBinding helperCode helperType
  have returnFromHelper : Steps P host ⟨s, f, expression putFn.body⟩ ⟨final, f, [constI32 3]⟩ :=
    forward.trans (enterHelper.trans helper.2)
  have throughLabel := (returnFromHelper.label (n := 1) (cont := [])).tail (Step.labelVals (vs := [.i32 3]))
  have leave : Step P host ⟨final, caller, [.frame 1 f [constI32 3]]⟩ ⟨final, caller, [constI32 3]⟩ :=
    Step.frameVals (vs := [.i32 3]) rfl
  exact enterPut.trans ((Steps.frame (f := caller) (n := 1) throughLabel).tail leave)

#print axioms scratchAddress_eq
#print axioms encode_three
#print axioms scratchBytes_eq
#print axioms putVarint_threeByte_of_helper

end SqliteWasm.ThreeByte
