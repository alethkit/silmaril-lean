module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.ModuleParts.Defs
public import Silmaril.Wasm.Execution.Core.Properties

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 65536

private def fastPut : List Instr :=
  [.localGet ⟨1⟩, .intConst .i64 127, .intRelOp .i64 (.gt .unsigned), .brIf ⟨0⟩,
    .localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i64 (some .i8) ⟨0⟩ memarg0,
    .intConst .i32 1, .return_]

theorem encode_one_byte (value : UInt64) (small : value.toNat < 128) :
    Varint.encode value = Silmaril.Formats.Bytes.ofList [UInt8.ofNat value.toNat] := by
  have small56 : value.toNat < 2 ^ 56 := by omega
  have small256 : value.toNat < 256 := by omega
  unfold Varint.encode
  dsimp only
  rw [ite_eq_left small56]
  simp [Varint.seven, small, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt small256]

private theorem fastPut_steps {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (locals : List ValType)
    (ptr : BitVec 32) (value : UInt64) (address : Nat) (mem : MemInst)
    (small : value.toNat < 128)
    (mapped : s.mem? (Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] locals) ⟨0⟩ =
      some (address, mem))
    (inBounds : ptr.toNat + 1 ≤ mem.bytes.size) :
    let f := Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] locals
    let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
    Steps P host ⟨s, f, expression fastPut⟩
      ⟨s.setMem address { mem with bytes := out }, f, [constI32 1, .plain .return_]⟩ := by
  dsimp only
  let f := Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] locals
  let word := Val.i64 value.toBitVec
  let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
  change Steps P host ⟨s, f, expression fastPut⟩
    ⟨s.setMem address { mem with bytes := out }, f, _⟩
  have getValue : Step P host ⟨s, f, [.plain (.localGet ⟨1⟩)]⟩ ⟨s, f, [word.toAdmin]⟩ :=
    .variable (.localGet rfl)
  have getPtr : Step P host ⟨s, f, [.plain (.localGet ⟨0⟩)]⟩ ⟨s, f, [(Val.i32 ptr).toAdmin]⟩ :=
    .variable (.localGet rfl)
  have compare : Step P host
      ⟨s, f, [word.toAdmin, .plain (.intConst .i64 127), .plain (.intRelOp .i64 (.gt .unsigned))]⟩
      ⟨s, f, [constI32 0]⟩ := by
    have below : ¬ 127 < value.toNat := by omega
    change Step P host ⟨s, f, [.plain (.intConst .i64 value.toBitVec),
      .plain (.intConst .i64 127), .plain (.intRelOp .i64 (.gt .unsigned))]⟩ ⟨s, f, [constI32 0]⟩
    simpa [Numerics.intRelOp, Numerics.bool32, IntType.width, below] using
      (Step.numeric (s := s) (f := f) (P := P) (host := host)
        (NumericStep.intRelOp (t := .i64) (op := .gt .unsigned) (x := value.toBitVec) (y := 127)))
  have branch : Step P host ⟨s, f, [constI32 0, .plain (.brIf ⟨0⟩)]⟩ ⟨s, f, []⟩ :=
    Step.brIfFalse
  have bytes : Memory.encodeLE 1 (value.toBitVec.setWidth 8).toNat =
      (Varint.encode value).data := by
    rw [encode_one_byte value small]
    have small256 : value.toNat < 256 := by omega
    simp [Memory.encodeLE, Nat.mod_eq_of_lt small256]
    rfl
  have store : Step P host
      ⟨s, f, [(Val.i32 ptr).toAdmin, word.toAdmin,
        .plain (.intStore .i64 (some .i8) ⟨0⟩ memarg0)]⟩
      ⟨s.setMem address { mem with bytes := out }, f, []⟩ := by
    apply Step.memory
    apply MemoryStep.storePackVal (a := .i32) mapped
    change Memory.store mem.bytes (ptr.toNat + 0) (count := 1) (value.toBitVec.setWidth 8) = some out
    rw [Nat.add_zero, Memory.store, Memory.writeBytes]
    rw [Memory.encodeLE_size]
    rw [ite_eq_left inBounds, bytes]
  let writeCode := expression [.localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i64 (some .i8) ⟨0⟩ memarg0]
  let ret := [constI32 1, Admin.plain .return_]
  have guard : Steps P host ⟨s, f, expression fastPut⟩ ⟨s, f, writeCode ++ ret⟩ :=
    (getValue.steps.ctxtInstrs (vs := []) (rest :=
        [.plain (.intConst .i64 127), .plain (.intRelOp .i64 (.gt .unsigned)), .plain (.brIf ⟨0⟩)]
          ++ writeCode ++ ret)).trans
      ((compare.steps.ctxtInstrs (vs := []) (rest := [.plain (.brIf ⟨0⟩)] ++ writeCode ++ ret)).trans
        (branch.steps.ctxtInstrs (vs := []) (rest := writeCode ++ ret)))
  have write : Steps P host ⟨s, f, writeCode⟩ ⟨s.setMem address { mem with bytes := out }, f, []⟩ :=
    (getPtr.steps.ctxtInstrs (vs := []) (rest :=
      [.plain (.localGet ⟨1⟩), .plain (.intStore .i64 (some .i8) ⟨0⟩ memarg0)])).trans
      ((getValue.steps.ctxtInstrs (vs := [.i32 ptr])
        (rest := [.plain (.intStore .i64 (some .i8) ⟨0⟩ memarg0)])).trans store.steps)
  exact guard.trans (write.ctxtInstrs (vs := []) (rest := ret))

private theorem putVarintBody_oneByte {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (caller : Frame) (callee : ModuleInst) (fn : Func)
    (ptr : BitVec 32) (value : UInt64) (address : Nat) (mem : MemInst)
    (head : fn.body.head? = some (.block .empty fastPut))
    (small : value.toNat < 128)
    (mapped : s.mem? (Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] fn.locals) ⟨0⟩ =
      some (address, mem))
    (inBounds : ptr.toNat + 1 ≤ mem.bytes.size) :
    let f := Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] fn.locals
    let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
    Steps P host ⟨s, caller, [.frame 1 f [.label 1 [] (expression fn.body)]]⟩
      ⟨s.setMem address { mem with bytes := out }, caller,
        [constI32 (BitVec.ofNat 32 (Varint.encode value).length)]⟩ := by
  dsimp only
  let f := Frame.forCall callee [.i32 ptr, .i64 value.toBitVec] fn.locals
  let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
  let t := s.setMem address { mem with bytes := out }
  have body : fn.body = .block .empty fastPut :: fn.body.tail := by
    cases h : fn.body with
    | nil => simp [h] at head
    | cons i is => simpa [h] using head
  have enter : Step P host ⟨s, f, [.plain (.block .empty fastPut)]⟩
      ⟨s, f, [.label 0 [] (expression fastPut)]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have exitLabel (arity : Nat) (rest : List Admin) :
      Step P host ⟨t, f, [.label arity [] ([constI32 1, .plain .return_] ++ rest)]⟩
        ⟨t, f, [constI32 1, .plain .return_]⟩ :=
    Step.returnLabel (vs := [.i32 1])
  have inner := fastPut_steps (P := P) (host := host) s callee fn.locals ptr value address mem
    small mapped inBounds
  have block := (enter.steps.trans (inner.label (n := 0) (cont := []))).tail (exitLabel 0 [])
  have withTail := Steps.ctxtInstrs (vs := []) (rest := expression fn.body.tail) block
  have withLabel := (Steps.label (n := 1) (cont := []) withTail).tail (exitLabel 1 (expression fn.body.tail))
  have exitFrame : Step P host
      ⟨t, caller, [.frame 1 f [constI32 1, .plain .return_]]⟩ ⟨t, caller, [constI32 1]⟩ :=
    Step.returnFrame (vs' := []) (vs := [.i32 1]) (rest := []) rfl
  have width : (Varint.encode value).length = 1 := by simp [encode_one_byte value small]
  rw [width]
  conv_lhs => rw [body]
  exact (Steps.frame (f := caller) (n := 1) withLabel).tail exitFrame

theorem putVarintSignature :
    sqlite.functionSignature? ⟨530⟩ =
      some ⟨[.num (.int .i32), .num (.int .i64)], [.num (.int .i32)]⟩ := rfl

private theorem putVarintFirstBlock :
    (definedFunction? sqlite 530).map (fun fn => fn.body.head?) =
      some (some (.block .empty fastPut)) := rfl

/-- The linked reactor function at index 530 writes the SQLite encoding of a one-byte value,
returns its width, and restores the caller frame. The caller's function slot must resolve to
the selected object code with its two-argument, one-result runtime type. Only the designated
memory instance is updated, through a one-byte splice at the supplied i32 address. -/
theorem putVarint_oneByte {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {ptr : BitVec 32} {value : UInt64} {memoryAddr : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 530 = some fn)
    (slot : caller.module.funcs[530]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (small : value.toNat < 128)
    (mapped : s.mem? (Frame.forCall fi.module [.i32 ptr, .i64 value.toBitVec] fn.locals) ⟨0⟩ =
      some (memoryAddr, mem))
    (inBounds : ptr.toNat + 1 ≤ mem.bytes.size) :
    let out := Memory.writeSlice mem.bytes ptr.toNat (Varint.encode value).data
    Steps P host ⟨s, caller, vals [.i32 ptr, .i64 value.toBitVec] ++ [.plain (.call ⟨530⟩)]⟩
      ⟨s.setMem memoryAddr { mem with bytes := out }, caller,
        [constI32 (BitVec.ofNat 32 (Varint.encode value).length)]⟩ := by
  have head := putVarintFirstBlock
  rw [selected] at head
  have enters := (Step.call (P := P) (host := host) (x := (⟨530⟩ : FuncIdx)) slot instanceAt).steps
  refine (enters.ctxtInstrs (vs := [.i32 ptr, .i64 value.toBitVec]) (rest := [])).trans ?_
  refine Relation.ReflTransGen.head
    (Step.callRefFunc (c := .callRefType fi.type) (vs := [.i32 ptr, .i64 value.toBitVec])
      trivial instanceAt signature rfl code) ?_
  exact putVarintBody_oneByte s caller fi.module fn ptr value memoryAddr mem
    (Option.some.inj head) small mapped inBounds

#print axioms putVarintSignature
#print axioms putVarint_oneByte

end SqliteWasm
