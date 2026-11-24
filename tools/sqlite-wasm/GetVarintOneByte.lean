module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.ModuleParts.Defs
import Silmaril.Wasm.Logic.Memory.Thms

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Core (bytesAt getElem?_bytesAt leNat_cons load_eq)
open Silmaril.Wasm.Validation (Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 65536

private def readerPrefix : List Instr :=
  [.localGet ⟨0⟩, .intLoad .i32 (some (.i8, .signed)) ⟨0⟩ memarg0, .localTee ⟨2⟩,
    .convert (.extend .unsigned), .intConst .i64 255, .intBinOp .i64 .and, .localSet ⟨3⟩]

private def readerBranch : List Instr :=
  [.localGet ⟨2⟩, .intConst .i32 (-1), .intRelOp .i32 (.le .signed), .brIf ⟨0⟩,
    .localGet ⟨0⟩, .localSet ⟨2⟩, .br ⟨1⟩]

private def readerSuffix : List Instr :=
  [.localGet ⟨1⟩, .localGet ⟨3⟩, .intStore .i64 none ⟨0⟩ ⟨3, 0⟩,
    .localGet ⟨2⟩, .localGet ⟨0⟩, .intBinOp .i32 .sub, .intConst .i32 1,
    .intBinOp .i32 .add, .intConst .i32 255, .intBinOp .i32 .and]

private def quotedReader : Func :=
  (definedFunction? sqlite 434).get rfl

private theorem quotedReaderSelected : definedFunction? sqlite 434 = some quotedReader := rfl

-- Keep the unexecuted remainder from the quote itself.
private def widerReader : List Instr :=
  match (quotedReader.body : List Instr)[7]? with
  | some (Instr.block .empty body) => body.tail
  | _ => []

private theorem quotedReaderBody : quotedReader.body =
    readerPrefix ++ .block .empty (.block .empty readerBranch :: widerReader) :: readerSuffix :=
  rfl

private abbrev readerFrame (callee : ModuleInst) (src dst : BitVec 32) : Frame :=
  Frame.forCall callee [.i32 src, .i32 dst] [.num (.int .i32), .num (.int .i64)]

private abbrev readerFrameWithByte (callee : ModuleInst) (src dst : BitVec 32) (byte : UInt8) :
    Frame :=
  ((readerFrame callee src dst).setLocal ⟨2⟩ (.i32 (BitVec.ofNat 32 byte.toNat))).setLocal
    ⟨3⟩ (.i64 (BitVec.ofNat 64 byte.toNat))

private theorem readSpec (B : ByteArray) (src : Nat) (byte : UInt8)
    (input : B[src]? = some byte) (small : byte.toNat < 128) :
    Varint.read? (File.View.ofBytes ⟨B⟩) src = some (UInt64.ofNat byte.toNat, src + 1) := by
  have bound := (getElem?_eq_some_iff.mp input).choose
  have viewByte : (File.View.ofBytes ⟨B⟩).get? src = some byte := by
    simpa [File.View.ofBytes, File.View.get?, Silmaril.Formats.Bytes.length, bound] using input
  simp [Varint.read?, Varint.readNat?, Varint.readAux?, viewByte, small, Nat.mod_eq_of_lt small]

private theorem loadByte (B : ByteArray) (src : Nat) (byte : UInt8)
    (input : B[src]? = some byte) :
    Memory.load B src 1 = some (BitVec.ofNat 8 byte.toNat) := by
  have bound := (getElem?_eq_some_iff.mp input).choose
  have pick : B.data.toList[src]? = some byte := by
    rw [getElem?_pos B src bound] at input
    simpa [ByteArray.getElem_eq_getElem_data, getElem?_pos B.data src (show src < B.data.size from bound)] using input
  have contents : bytesAt B ⟨src, 1⟩ = [byte] := by
    apply List.ext_getElem?
    intro i
    cases i <;> simp [getElem?_bytesAt, pick]
  rw [load_eq (by omega), contents, leNat_cons]
  rfl

private theorem prefixSteps {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (src dst : BitVec 32) (byte : UInt8)
    (address : Nat) (mem : MemInst)
    (mapped : s.mem? (readerFrame callee src dst) ⟨0⟩ = some (address, mem))
    (input : mem.bytes[src.toNat]? = some byte) (small : byte.toNat < 128) :
    Steps P host ⟨s, readerFrame callee src dst, expression readerPrefix⟩
      ⟨s, readerFrameWithByte callee src dst byte, []⟩ := by
  let f := readerFrame callee src dst
  let lo := BitVec.ofNat 32 byte.toNat
  let hi := BitVec.ofNat 64 byte.toNat
  let g := f.setLocal ⟨2⟩ (.i32 lo)
  have get : Step P host ⟨s, f, expression [.localGet ⟨0⟩]⟩ ⟨s, f, vals [.i32 src]⟩ :=
    .variable (.localGet rfl)
  have sign : (BitVec.ofNat 8 byte.toNat).signExtend 32 = lo := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false]
    · apply BitVec.eq_of_toNat_eq
      simp [lo]
    · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
      simp [show 2 * byte.toNat < 256 by omega]
  have load : Step P host
      ⟨s, f, vals [.i32 src] ++ expression [.intLoad .i32 (some (.i8, .signed)) ⟨0⟩ memarg0]⟩
      ⟨s, f, vals [.i32 lo]⟩ := by
    rw [← sign]
    exact .memory (MemoryStep.loadPackVal (a := .i32) mapped (by
      change Memory.load mem.bytes (src.toNat + 0) 1 = _
      rw [Nat.add_zero]
      exact loadByte mem.bytes src.toNat byte input))
  have tee : Step P host ⟨s, f, vals [.i32 lo] ++ expression [.localTee ⟨2⟩]⟩
      ⟨s, f, vals [.i32 lo, .i32 lo] ++ expression [.localSet ⟨2⟩]⟩ :=
    .variable .localTee
  have setByte : Step P host ⟨s, f, vals [.i32 lo] ++ expression [.localSet ⟨2⟩]⟩ ⟨s, g, []⟩ :=
    .variable (.localSet (by change 2 < 4; decide))
  have extend : Step P host ⟨s, g, vals [.i32 lo] ++ expression [.convert (.extend .unsigned)]⟩
      ⟨s, g, vals [.i64 hi]⟩ := by
    apply Step.numeric
    apply NumericStep.convert (op := .extend .unsigned)
    have widen : lo.setWidth 64 = hi := by
      apply BitVec.eq_of_toNat_eq
      simp [lo, hi]
    cases policy : P.nan <;>
      simp only [Numerics.convertP, policy, Numerics.convertRel, Numerics.convert] <;>
      exact congrArg Except.ok widen.symm
  have mask : Step P host ⟨s, g, vals [.i64 hi, .i64 255] ++ expression [.intBinOp .i64 .and]⟩
      ⟨s, g, vals [.i64 hi]⟩ := by
    apply Step.numeric
    apply NumericStep.intBinOp (t := .i64)
    change Except.ok (hi &&& 255#64) = Except.ok hi
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change hi.toNat &&& (2^8 - 1) = hi.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod]
    apply Nat.mod_eq_of_lt
    simp [hi]
    omega
  have setValue : Step P host ⟨s, g, vals [.i64 hi] ++ expression [.localSet ⟨3⟩]⟩
      ⟨s, readerFrameWithByte callee src dst byte, []⟩ :=
    .variable (.localSet (by change 3 < 4; decide))
  let finish := expression [.convert (.extend .unsigned), .intConst .i64 255,
    .intBinOp .i64 .and, .localSet ⟨3⟩]
  refine (get.steps.ctxtInstrs (vs := []) (rest :=
    expression [.intLoad .i32 (some (.i8, .signed)) ⟨0⟩ memarg0, .localTee ⟨2⟩] ++ finish)).trans ?_
  refine (load.steps.ctxtInstrs (vs := []) (rest := expression [.localTee ⟨2⟩] ++ finish)).trans ?_
  refine (tee.steps.ctxtInstrs (vs := []) (rest := finish)).trans ?_
  refine (setByte.steps.ctxtInstrs (vs := [.i32 lo]) (rest := finish)).trans ?_
  refine (extend.steps.ctxtInstrs (vs := []) (rest :=
    expression [.intConst .i64 255, .intBinOp .i64 .and, .localSet ⟨3⟩])).trans ?_
  exact (mask.steps.ctxtInstrs (vs := []) (rest := expression [.localSet ⟨3⟩])).tail setValue

private theorem branchSteps {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (src dst : BitVec 32) (byte : UInt8)
    (small : byte.toNat < 128) :
    let f := readerFrameWithByte callee src dst byte
    let g := f.setLocal ⟨2⟩ (.i32 src)
    Steps P host ⟨s, f, expression readerBranch⟩ ⟨s, g, expression [.br ⟨1⟩]⟩ := by
  dsimp only
  let f := readerFrameWithByte callee src dst byte
  let lo := BitVec.ofNat 32 byte.toNat
  have getByte : Step P host ⟨s, f, expression [.localGet ⟨2⟩]⟩ ⟨s, f, vals [.i32 lo]⟩ :=
    .variable (.localGet rfl)
  have compare : Step P host
      ⟨s, f, vals [.i32 lo, .i32 (-1)] ++ expression [.intRelOp .i32 (.le .signed)]⟩
      ⟨s, f, [constI32 0]⟩ := by
    have loNat : lo.toNat = byte.toNat := by simp [lo]
    have nonnegative : lo.toInt = (lo.toNat : Int) :=
      BitVec.toInt_eq_toNat_of_lt (by rw [loNat]; omega)
    have test : Numerics.intRelOp .i32 (.le .signed) lo (-1) = 0 := by
      change Numerics.bool32 (decide (lo.toInt ≤ (-1#32).toInt)) = 0
      rw [nonnegative, show (-1#32).toInt = -1 from rfl]
      have negative : ¬ (lo.toNat : Int) ≤ -1 := by omega
      simp [Numerics.bool32, negative]
    rw [← test]
    exact .numeric (NumericStep.intRelOp (t := .i32) (op := .le .signed) (x := lo) (y := -1))
  have getSrc : Step P host ⟨s, f, expression [.localGet ⟨0⟩]⟩ ⟨s, f, vals [.i32 src]⟩ :=
    .variable (.localGet rfl)
  have setSrc : Step P host ⟨s, f, vals [.i32 src] ++ expression [.localSet ⟨2⟩]⟩
      ⟨s, f.setLocal ⟨2⟩ (.i32 src), []⟩ :=
    .variable (.localSet (by change 2 < 4; decide))
  let finish := expression [.localGet ⟨0⟩, .localSet ⟨2⟩, .br ⟨1⟩]
  refine (getByte.steps.ctxtInstrs (vs := []) (rest :=
    expression [.intConst .i32 (-1), .intRelOp .i32 (.le .signed), .brIf ⟨0⟩] ++ finish)).trans ?_
  refine (compare.steps.ctxtInstrs (vs := []) (rest := expression [.brIf ⟨0⟩] ++ finish)).trans ?_
  refine (Step.brIfFalse.steps.ctxtInstrs (vs := []) (rest := finish)).trans ?_
  refine (getSrc.steps.ctxtInstrs (vs := []) (rest := expression [.localSet ⟨2⟩, .br ⟨1⟩])).trans ?_
  exact setSrc.steps.ctxtInstrs (vs := []) (rest := expression [.br ⟨1⟩])

private theorem blockSteps {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (src dst : BitVec 32) (byte : UInt8)
    (small : byte.toNat < 128) :
    let f := readerFrameWithByte callee src dst byte
    let g := f.setLocal ⟨2⟩ (.i32 src)
    Steps P host ⟨s, f, expression [.block .empty (.block .empty readerBranch :: widerReader)]⟩
      ⟨s, g, []⟩ := by
  dsimp only
  let f := readerFrameWithByte callee src dst byte
  let g := f.setLocal ⟨2⟩ (.i32 src)
  let rest := expression widerReader
  have enterOuter : Step P host
      ⟨s, f, expression [.block .empty (.block .empty readerBranch :: widerReader)]⟩
      ⟨s, f, [.label 0 [] (expression (.block .empty readerBranch :: widerReader))]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have enterInner : Step P host ⟨s, f, expression [.block .empty readerBranch]⟩
      ⟨s, f, [.label 0 [] (expression readerBranch)]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have exitInner : Step P host ⟨s, g, [.label 0 [] (expression [.br ⟨1⟩])]⟩
      ⟨s, g, expression [.br ⟨0⟩]⟩ :=
    Step.brLabelSucc (vs := []) (rest := []) (by decide)
  have exitOuter : Step P host ⟨s, g, [.label 0 [] (expression [.br ⟨0⟩] ++ rest)]⟩
      ⟨s, g, []⟩ :=
    Step.brLabelZero (vs' := []) (vs := []) rfl rfl
  have branch := branchSteps (P := P) (host := host) s callee src dst byte small
  have inner := (enterInner.steps.trans (branch.label (n := 0) (cont := []))).tail exitInner
  exact (enterOuter.steps.trans
    ((Steps.ctxtInstrs (vs := []) (rest := rest) inner).label (n := 0) (cont := []))).tail exitOuter

private theorem suffixSteps {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (callee : ModuleInst) (src dst : BitVec 32) (byte : UInt8)
    (address : Nat) (mem : MemInst)
    (mapped : s.mem? (readerFrame callee src dst) ⟨0⟩ = some (address, mem))
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    let f := (readerFrameWithByte callee src dst byte).setLocal ⟨2⟩ (.i32 src)
    let out := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 byte.toNat)
    Steps P host ⟨s, f, expression readerSuffix⟩
      ⟨s.setMem address { mem with bytes := out }, f, [constI32 1]⟩ := by
  dsimp only
  let f := (readerFrameWithByte callee src dst byte).setLocal ⟨2⟩ (.i32 src)
  let hi := BitVec.ofNat 64 byte.toNat
  let out := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 byte.toNat)
  let t := s.setMem address { mem with bytes := out }
  let storeInstr := Instr.intStore .i64 none ⟨0⟩ ⟨3, 0⟩
  have getDst : Step P host ⟨s, f, expression [.localGet ⟨1⟩]⟩ ⟨s, f, vals [.i32 dst]⟩ :=
    .variable (.localGet rfl)
  have getValue : Step P host ⟨s, f, expression [.localGet ⟨3⟩]⟩ ⟨s, f, vals [.i64 hi]⟩ :=
    .variable (.localGet rfl)
  have store : Step P host ⟨s, f, vals [.i32 dst, .i64 hi] ++ expression [storeInstr]⟩
      ⟨t, f, []⟩ := by
    apply Step.memory
    apply MemoryStep.storeIntVal (a := .i32) (show s.mem? f ⟨0⟩ = some (address, mem) from mapped)
    change Memory.store mem.bytes (dst.toNat + 0) (count := 8) (hi.setWidth 64) = some out
    rw [Nat.add_zero, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left inBounds]
    simp [hi, out]
  have getEnd : Step P host ⟨t, f, expression [.localGet ⟨2⟩]⟩ ⟨t, f, vals [.i32 src]⟩ :=
    .variable (.localGet rfl)
  have getSrc : Step P host ⟨t, f, expression [.localGet ⟨0⟩]⟩ ⟨t, f, vals [.i32 src]⟩ :=
    .variable (.localGet rfl)
  have sub : Step P host
      ⟨t, f, vals [.i32 src, .i32 src] ++ expression [.intBinOp .i32 .sub]⟩
      ⟨t, f, [constI32 0]⟩ :=
    .numeric (NumericStep.intBinOp (t := .i32) (op := .sub) (by
      change Except.ok (src - src) = Except.ok 0#32
      rw [BitVec.sub_self]))
  have add : Step P host
      ⟨t, f, vals [.i32 0, .i32 1] ++ expression [.intBinOp .i32 .add]⟩ ⟨t, f, [constI32 1]⟩ :=
    .numeric (NumericStep.intBinOp (t := .i32) (op := .add) rfl)
  have mask : Step P host
      ⟨t, f, vals [.i32 1, .i32 255] ++ expression [.intBinOp .i32 .and]⟩
      ⟨t, f, [constI32 1]⟩ :=
    .numeric (NumericStep.intBinOp (t := .i32) (op := .and) rfl)
  let maskCode := expression [.intConst .i32 255, .intBinOp .i32 .and]
  let addCode := expression [.intConst .i32 1, .intBinOp .i32 .add] ++ maskCode
  let countCode := expression [.localGet ⟨2⟩, .localGet ⟨0⟩, .intBinOp .i32 .sub] ++ addCode
  refine (getDst.steps.ctxtInstrs (vs := []) (rest :=
    expression [.localGet ⟨3⟩, storeInstr] ++ countCode)).trans ?_
  refine (getValue.steps.ctxtInstrs (vs := [.i32 dst]) (rest := expression [storeInstr] ++ countCode)).trans ?_
  refine (store.steps.ctxtInstrs (vs := []) (rest := countCode)).trans ?_
  refine (getEnd.steps.ctxtInstrs (vs := []) (rest :=
    expression [.localGet ⟨0⟩, .intBinOp .i32 .sub] ++ addCode)).trans ?_
  refine (getSrc.steps.ctxtInstrs (vs := [.i32 src]) (rest :=
    expression [.intBinOp .i32 .sub] ++ addCode)).trans ?_
  refine (sub.steps.ctxtInstrs (vs := []) (rest := addCode)).trans ?_
  exact (add.steps.ctxtInstrs (vs := []) (rest := maskCode)).tail mask

private theorem readerBodySteps {H : Type} {P : Profile} {host : HostSemantics H}
    (s : Store H) (caller : Frame) (callee : ModuleInst) (src dst : BitVec 32) (byte : UInt8)
    (address : Nat) (mem : MemInst)
    (mapped : s.mem? (readerFrame callee src dst) ⟨0⟩ = some (address, mem))
    (input : mem.bytes[src.toNat]? = some byte) (small : byte.toNat < 128)
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    let f := Frame.forCall callee [.i32 src, .i32 dst] quotedReader.locals
    let out := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 byte.toNat)
    Steps P host ⟨s, caller, [.frame 1 f [.label 1 [] (expression quotedReader.body)]]⟩
      ⟨s.setMem address { mem with bytes := out }, caller, [constI32 1]⟩ := by
  dsimp only
  let block := Instr.block .empty (.block .empty readerBranch :: widerReader)
  have loaded := prefixSteps (P := P) (host := host) s callee src dst byte address mem mapped input small
  have branch := blockSteps (P := P) (host := host) s callee src dst byte small
  have suffix := suffixSteps (P := P) (host := host) s callee src dst byte address mem mapped inBounds
  have body := (loaded.ctxtInstrs (vs := []) (rest := expression (block :: readerSuffix))).trans
    ((branch.ctxtInstrs (vs := []) (rest := expression readerSuffix)).trans suffix)
  have closed := (Steps.label (n := 1) (cont := []) body).tail (Step.labelVals (vs := [.i32 1]))
  conv_lhs => rw [quotedReaderBody, expression, List.map_append]
  exact (Steps.frame (f := caller) (n := 1) closed).tail (Step.frameVals (vs := [.i32 1]) rfl)

theorem getVarintSignature :
    sqlite.functionSignature? ⟨434⟩ =
      some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩ := rfl

/-- If the caller's slot 434 resolves to the selected reactor code with the stated runtime
type, and its memory 0 contains a byte below 128 at `src` and eight writable bytes at `dst`,
the one-byte reader follows `Varint.read?` on the initial memory. It reads before writing,
so the source may overlap the destination. Its sole store effect is the eight-byte
little-endian splice in that memory instance. The call returns i32 1 in the original frame. -/
theorem getVarint_oneByte {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {src dst : BitVec 32} {byte : UInt8} {memoryAddr : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 434 = some fn)
    (slot : caller.module.funcs[434]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)))
    (mapped : s.mem? { module := fi.module } ⟨0⟩ = some (memoryAddr, mem))
    (input : mem.bytes[src.toNat]? = some byte)
    (small : byte.toNat < 128)
    (inBounds : dst.toNat + 8 ≤ mem.bytes.size) :
    Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat =
        some (UInt64.ofNat byte.toNat, src.toNat + 1) ∧
    Steps P host ⟨s, caller, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 byte.toNat) },
        caller, [constI32 1]⟩ := by
  have eq := Option.some.inj (selected.symm.trans quotedReaderSelected)
  subst fn
  refine ⟨readSpec mem.bytes src.toNat byte input small, ?_⟩
  have enters := (Step.call (P := P) (host := host) (x := (⟨434⟩ : FuncIdx)) slot instanceAt).steps
  refine (enters.ctxtInstrs (vs := [.i32 src, .i32 dst]) (rest := [])).trans ?_
  refine Relation.ReflTransGen.head
    (Step.callRefFunc (c := .callRefType fi.type) (vs := [.i32 src, .i32 dst])
      trivial instanceAt signature rfl code) ?_
  exact readerBodySteps s caller fi.module src dst byte memoryAddr mem mapped input small inBounds

#print axioms getVarintSignature
#print axioms getVarint_oneByte

end SqliteWasm
