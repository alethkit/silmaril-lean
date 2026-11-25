module

public import SqliteWasm.WholeModule
public import SqliteWasmArtifactEntries
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.ModuleParts.Defs
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def threadSetupFunction : Func := (definedFunction? sqlite 1516).get rfl

private def i32 (v : BitVec 32) : Instr := .intConst .i32 v
private def load (off : Fin (2 ^ 64)) : Instr := .intLoad .i32 none ⟨0⟩ ⟨2, off⟩
private def store (off : Fin (2 ^ 64)) : Instr := .intStore .i32 none ⟨0⟩ ⟨2, off⟩

private def heapSpan : List Instr :=
  [i32 126112, i32 60576, .intBinOp .i32 .sub]

private def staticSpan : List Instr :=
  [i32 126112, .intTestOp .i32 .eqz, .brIf ⟨0⟩] ++
    heapSpan ++ [.localSet ⟨1⟩, .br ⟨1⟩]

private def fallbackSpan : List Instr :=
  [.globalGet ⟨0⟩, .localSet ⟨1⟩] ++ heapSpan ++
    [i32 1024, .localGet ⟨1⟩, i32 1024, .intRelOp .i32 (.gt .unsigned),
      .localTee ⟨0⟩, .select none, .localSet ⟨1⟩,
      i32 126112, i32 1024, .localGet ⟨0⟩, .select none, .localSet ⟨0⟩]

private def threadPrefix : List Instr :=
  [i32 0, i32 59924, store 59924, i32 126112, .localSet ⟨0⟩,
    .block .empty (.block .empty staticSpan :: fallbackSpan)]

private def threadFields : List Instr :=
  [i32 56, i32 0, store 59924,
    i32 52, .localGet ⟨1⟩, store 59924,
    i32 48, .localGet ⟨0⟩, store 59924,
    i32 8, i32 59924, store 59924,
    i32 4, i32 59924, store 59924]

private def copyField : List Instr := [i32 12, i32 0, load 59892, store 59924]

private def recordSpan : List Instr :=
  [i32 0, .localGet ⟨1⟩, i32 8388608,
    .localGet ⟨1⟩, i32 8388608, .intRelOp .i32 (.lt .unsigned), .select none, store 59320]

private def threadSuffix : List Instr := threadFields ++ copyField ++ recordSpan

private theorem actualBody : threadSetupFunction.body = threadPrefix ++ threadSuffix := rfl

private theorem actualLocals : threadSetupFunction.locals = [.num (.int .i32), .num (.int .i32)] :=
  rfl

theorem originalThreadSetupFunction :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      definedFunction? m 1516) = some threadSetupFunction := by
  rw [originalDecode]
  rfl

private def writeWord (mem : MemInst) (offset : Nat) (word : BitVec 32) : MemInst :=
  { mem with bytes := Memory.writeSlice mem.bytes offset (Memory.encodeLE 4 word.toNat) }

private theorem writeWord_step {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {address : Nat} {off : Fin (2 ^ 64)} {mem : MemInst} {ptr word : BitVec 32}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (bound : ptr.toNat + off.val + 4 ≤ mem.bytes.size) :
    Step P host ⟨s, f, [constI32 ptr, constI32 word, .plain (store off)]⟩
      ⟨s.setMem address (writeWord mem (ptr.toNat + off.val) word), f, []⟩ := by
  apply Step.memory
  refine MemoryStep.storeIntVal (t := .i32) (arg := ⟨2, off⟩)
    (a := .i32) (i := ptr) (c := word) mapped ?_
  have cast : word.setWidth 32 = word := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt word.isLt]
  change Memory.store mem.bytes (ptr.toNat + off.val) (count := 4) (word.setWidth 32) = _
  rw [cast]
  rw [Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bound]

private theorem writeWord_size (mem : MemInst) (offset : Nat) (word : BitVec 32)
    (bound : offset + 4 ≤ mem.bytes.size) :
    (writeWord mem offset word).bytes.size = mem.bytes.size := by
  apply Memory.writeBytes_size mem.bytes (Memory.encodeLE 4 word.toNat) _ offset
  simp [Memory.writeBytes, writeWord, bound]

private theorem mapped_after_write {H : Type} {s : Store H} {f f' : Frame} {address : Nat}
    {mem mem' : MemInst} (sameModule : f'.module = f.module)
    (mapped : s.mem? f ⟨0⟩ = some (address, mem)) :
    (s.setMem address mem').mem? f' ⟨0⟩ = some (address, mem') := by
  change (f.module.mems[(0 : Nat)]?.bind fun a =>
    s.mems[a]?.bind (fun m => some (a, m))) = some (address, mem) at mapped
  change (f'.module.mems[(0 : Nat)]?.bind fun a =>
    (s.setMem address mem').mems[a]?.bind (fun m => some (a, m))) = some (address, mem')
  obtain ⟨a, hf, mapped⟩ := Option.bind_eq_some_iff.mp mapped
  obtain ⟨m, hs, equal⟩ := Option.bind_eq_some_iff.mp mapped
  simp only [Option.some.injEq, Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  rw [sameModule, hf, Option.bind_some]
  simp [Store.setMem, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hs).1]

private def setupFrame (m : ModuleInst) (a b : BitVec 32) : Frame :=
  ⟨[some (.i32 a), some (.i32 b)], m⟩

private theorem staticSpanSteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : ModuleInst} :
    Steps P host ⟨s, setupFrame m 126112 0, expression [.block .empty staticSpan]⟩
      ⟨s, setupFrame m 126112 65536, [.plain (.br ⟨0⟩)]⟩ := by
  let f := setupFrame m 126112 0
  let f' := setupFrame m 126112 65536
  have enter : Step P host ⟨s, f, expression [.block .empty staticSpan]⟩
      ⟨s, f, [.label 0 [] (expression staticSpan)]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have test : Step P host ⟨s, f, expression [i32 126112, .intTestOp .i32 .eqz]⟩
      ⟨s, f, [constI32 0]⟩ :=
    .numeric (.intTestOp (t := .i32) (op := .eqz) (x := 126112))
  have skip : Step P host ⟨s, f, [constI32 0, .plain (.brIf ⟨0⟩)]⟩ ⟨s, f, []⟩ :=
    Step.brIfFalse
  have sub : Step P host ⟨s, f, expression heapSpan⟩ ⟨s, f, [constI32 65536]⟩ :=
    .numeric (.intBinOp (t := .i32) (op := .sub) (x := 126112) (y := 60576) rfl)
  have assign : Step P host ⟨s, f, [constI32 65536, .plain (.localSet ⟨1⟩)]⟩
      ⟨s, f', []⟩ :=
    .variable (.localSet (v := .i32 65536) (x := ⟨1⟩) (show 1 < 2 by decide))
  have run : Steps P host ⟨s, f, expression staticSpan⟩
      ⟨s, f', [.plain (.br ⟨1⟩)]⟩ := by
    refine (test.steps.ctxtInstrs (vs := []) (rest := expression
      ([.brIf ⟨0⟩] ++ heapSpan ++ [.localSet ⟨1⟩, .br ⟨1⟩]))).trans ?_
    refine (skip.steps.ctxtInstrs (vs := []) (rest := expression
      (heapSpan ++ [.localSet ⟨1⟩, .br ⟨1⟩]))).trans ?_
    refine (sub.steps.ctxtInstrs (vs := []) (rest := expression
      [.localSet ⟨1⟩, .br ⟨1⟩])).trans ?_
    exact assign.steps.ctxtInstrs (vs := []) (rest := expression [.br ⟨1⟩])
  have exit : Step P host ⟨s, f', [.label 0 [] [.plain (.br ⟨1⟩)]]⟩
      ⟨s, f', [.plain (.br ⟨0⟩)]⟩ := Step.brLabelSucc (vs := []) (rest := []) (by decide)
  exact (enter.steps.trans (run.label (n := 0) (cont := []))).tail exit

private theorem setupSpanSteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : ModuleInst} :
    Steps P host ⟨s, setupFrame m 126112 0,
      expression [.block .empty (.block .empty staticSpan :: fallbackSpan)]⟩
      ⟨s, setupFrame m 126112 65536, []⟩ := by
  let f := setupFrame m 126112 0
  let f' := setupFrame m 126112 65536
  have enter : Step P host
      ⟨s, f, expression [.block .empty (.block .empty staticSpan :: fallbackSpan)]⟩
      ⟨s, f, [.label 0 [] (expression (.block .empty staticSpan :: fallbackSpan))]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have run : Steps P host ⟨s, f, expression (.block .empty staticSpan :: fallbackSpan)⟩
      ⟨s, f', .plain (.br ⟨0⟩) :: expression fallbackSpan⟩ :=
    (staticSpanSteps (P := P) (host := host)).ctxtInstrs (vs := []) (rest := expression fallbackSpan)
  have exit : Step P host ⟨s, f', [.label 0 [] (.plain (.br ⟨0⟩) :: expression fallbackSpan)]⟩
      ⟨s, f', []⟩ := Step.brLabelZero (vs' := []) (vs := []) rfl rfl
  exact (enter.steps.trans (run.label (n := 0) (cont := []))).tail exit

private theorem threadPrefixSteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : ModuleInst} {address : Nat} {mem : MemInst}
    (mapped : s.mem? (Frame.forCall m [] threadSetupFunction.locals) ⟨0⟩ = some (address, mem))
    (bound : 59928 ≤ mem.bytes.size) :
    Steps P host ⟨s, Frame.forCall m [] threadSetupFunction.locals, expression threadPrefix⟩
      ⟨s.setMem address (writeWord mem 59924 59924), setupFrame m 126112 65536, []⟩ := by
  let f := Frame.forCall m [] threadSetupFunction.locals
  let s' := s.setMem address (writeWord mem 59924 59924)
  have memory : Step P host ⟨s, f, expression [i32 0, i32 59924, store 59924]⟩ ⟨s', f, []⟩ :=
    writeWord_step (off := 59924) (ptr := 0) (word := 59924) mapped bound
  have assign : Step P host ⟨s', f, expression [i32 126112, .localSet ⟨0⟩]⟩
      ⟨s', setupFrame m 126112 0, []⟩ := by
    have localBound : (0 : Nat) < f.locals.length := show 0 < 2 by decide
    exact .variable (.localSet (v := .i32 126112) (x := ⟨0⟩) localBound)
  refine (memory.steps.ctxtInstrs (vs := []) (rest := expression
    [i32 126112, .localSet ⟨0⟩, .block .empty (.block .empty staticSpan :: fallbackSpan)])).trans ?_
  refine (assign.steps.ctxtInstrs (vs := []) (rest := expression
    [.block .empty (.block .empty staticSpan :: fallbackSpan)])).trans ?_
  exact setupSpanSteps

private theorem setMem_twice {H : Type} (s : Store H) (address : Nat) (mem mem' : MemInst) :
    (s.setMem address mem).setMem address mem' = s.setMem address mem' := by
  simp [Store.setMem, List.set_set]

private theorem constThreadWrite {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {address : Nat} {mem : MemInst} {ptr word : BitVec 32}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (bound : ptr.toNat + 59924 + 4 ≤ mem.bytes.size) :
    Steps P host ⟨s, f, expression [i32 ptr, i32 word, store 59924]⟩
      ⟨s.setMem address (writeWord mem (ptr.toNat + 59924) word), f, []⟩ :=
  (writeWord_step (off := 59924) mapped bound).steps

private theorem localThreadWrite {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {address : Nat} {mem : MemInst} {ptr word : BitVec 32} {x : LocalIdx}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (bound : ptr.toNat + 59924 + 4 ≤ mem.bytes.size)
    (localValue : f.local? x = some (some (.i32 word))) :
    Steps P host ⟨s, f, expression [i32 ptr, .localGet x, store 59924]⟩
      ⟨s.setMem address (writeWord mem (ptr.toNat + 59924) word), f, []⟩ := by
  have get : Step P host ⟨s, f, [.plain (.localGet x)]⟩ ⟨s, f, [constI32 word]⟩ :=
    .variable (.localGet localValue)
  exact (get.steps.ctxtInstrs (vs := [.i32 ptr]) (rest := [.plain (store 59924)])).trans
    (constThreadWrite mapped bound)

private def threadFieldsMemory (mem : MemInst) : MemInst :=
  writeWord (writeWord (writeWord (writeWord (writeWord
    mem 59980 0) 59976 65536) 59972 126112) 59932 59924) 59928 59924

private theorem threadFieldsSteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : ModuleInst} {address : Nat} {mem : MemInst}
    (mapped : s.mem? (setupFrame m 126112 65536) ⟨0⟩ = some (address, mem))
    (bound : 59984 ≤ mem.bytes.size) :
    Steps P host ⟨s, setupFrame m 126112 65536, expression threadFields⟩
      ⟨s.setMem address (threadFieldsMemory mem), setupFrame m 126112 65536, []⟩ := by
  let f := setupFrame m 126112 65536
  let mem1 := writeWord mem 59980 0
  let mem2 := writeWord mem1 59976 65536
  let mem3 := writeWord mem2 59972 126112
  let mem4 := writeWord mem3 59932 59924
  let mem5 := writeWord mem4 59928 59924
  have bound1 : 59984 ≤ mem1.bytes.size := by
    rw [writeWord_size mem 59980 0 bound]
    exact bound
  have bound2 : 59984 ≤ mem2.bytes.size := by
    rw [writeWord_size mem1 59976 65536 (by omega)]
    exact bound1
  have bound3 : 59984 ≤ mem3.bytes.size := by
    rw [writeWord_size mem2 59972 126112 (by omega)]
    exact bound2
  have bound4 : 59984 ≤ mem4.bytes.size := by
    rw [writeWord_size mem3 59932 59924 (by omega)]
    exact bound3
  have lookup : ∀ current : MemInst, (s.setMem address current).mem? f ⟨0⟩ = some (address, current) :=
    fun _ => mapped_after_write rfl mapped
  let f1 := [i32 56, i32 0, store 59924]
  let f2 := [i32 52, .localGet ⟨1⟩, store 59924]
  let f3 := [i32 48, .localGet ⟨0⟩, store 59924]
  let f4 := [i32 8, i32 59924, store 59924]
  let f5 := [i32 4, i32 59924, store 59924]
  have w1 : Steps P host ⟨s, f, expression f1⟩ ⟨s.setMem address mem1, f, []⟩ :=
    constThreadWrite (ptr := 56) (word := 0) mapped bound
  have w2 : Steps P host ⟨s.setMem address mem1, f, expression f2⟩
      ⟨s.setMem address mem2, f, []⟩ := by
    have run := localThreadWrite (P := P) (host := host) (ptr := 52) (word := 65536)
      (x := ⟨1⟩) (lookup mem1) (show 59980 ≤ mem1.bytes.size by omega) rfl
    rw [setMem_twice] at run
    exact run
  have w3 : Steps P host ⟨s.setMem address mem2, f, expression f3⟩
      ⟨s.setMem address mem3, f, []⟩ := by
    have run := localThreadWrite (P := P) (host := host) (ptr := 48) (word := 126112)
      (x := ⟨0⟩) (lookup mem2) (show 59976 ≤ mem2.bytes.size by omega) rfl
    rw [setMem_twice] at run
    exact run
  have w4 : Steps P host ⟨s.setMem address mem3, f, expression f4⟩
      ⟨s.setMem address mem4, f, []⟩ := by
    have run := constThreadWrite (P := P) (host := host) (ptr := 8) (word := 59924)
      (lookup mem3) (show 59936 ≤ mem3.bytes.size by omega)
    rw [setMem_twice] at run
    exact run
  have w5 : Steps P host ⟨s.setMem address mem4, f, expression f5⟩
      ⟨s.setMem address mem5, f, []⟩ := by
    have run := constThreadWrite (P := P) (host := host) (ptr := 4) (word := 59924)
      (lookup mem4) (show 59932 ≤ mem4.bytes.size by omega)
    rw [setMem_twice] at run
    exact run
  change Steps P host ⟨s, f, expression f1 ++ expression f2 ++ expression f3 ++
    expression f4 ++ expression f5⟩ ⟨s.setMem address mem5, f, []⟩
  simp only [List.append_assoc]
  refine (w1.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (w2.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (w3.ctxtInstrs (vs := []) (rest := _)).trans ?_
  exact (w4.ctxtInstrs (vs := []) (rest := _)).trans w5

private def prefixWrites : List (Nat × BitVec 32) :=
  [(59924, 59924), (59980, 0), (59976, 65536), (59972, 126112), (59932, 59924), (59928, 59924)]

private def applyWrites (mem : MemInst) (writes : List (Nat × BitVec 32)) : MemInst :=
  writes.foldl (fun current (offset, word) => writeWord current offset word) mem

private theorem applyWrites_preserve (mem : MemInst) (writes : List (Nat × BitVec 32))
    (within : ∀ p ∈ writes, 59896 ≤ p.1 ∧ p.1 + 4 ≤ mem.bytes.size) :
    (applyWrites mem writes).bytes.size = mem.bytes.size ∧
    Memory.load (applyWrites mem writes).bytes 59892 4 = Memory.load mem.bytes 59892 4 := by
  induction writes generalizing mem with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
    obtain ⟨offset, word⟩ := entry
    obtain ⟨separate, bound⟩ := within (offset, word) List.mem_cons_self
    let next := writeWord mem offset word
    have size := writeWord_size mem offset word bound
    obtain ⟨sizes, same⟩ := ih next fun p hp => by
      obtain ⟨outside, fits⟩ := within p (List.mem_cons_of_mem _ hp)
      exact ⟨outside, size.symm ▸ fits⟩
    have wrote : Memory.writeBytes mem.bytes offset (Memory.encodeLE 4 word.toNat) =
        some next.bytes := by simp [Memory.writeBytes, next, writeWord, bound]
    have read := Memory.readBytes_writeBytes_disjoint _ _ _ offset 59892 4 wrote (Or.inl separate)
    constructor
    · exact sizes.trans size
    · change Memory.load (applyWrites next rest).bytes 59892 4 = _
      rw [same]
      unfold Memory.load
      rw [read]

private theorem threadCopySteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {address : Nat} {mem : MemInst} {word : BitVec 32}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (bound : 59940 ≤ mem.bytes.size)
    (loaded : Memory.load mem.bytes 59892 4 = some word) :
    Steps P host ⟨s, f, expression copyField⟩
      ⟨s.setMem address (writeWord mem 59936 word), f, []⟩ := by
  have cast : word.setWidth 32 = word := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt word.isLt]
  have read : Step P host ⟨s, f, expression [i32 0, load 59892]⟩
      ⟨s, f, [constI32 (word.setWidth 32)]⟩ :=
    .memory (MemoryStep.loadIntVal (t := .i32) (a := .i32) (i := 0) (arg := ⟨2, 59892⟩)
      (c := word) mapped loaded)
  rw [cast] at read
  exact (read.steps.ctxtInstrs (vs := [.i32 12]) (rest := [.plain (store 59924)])).tail
    (writeWord_step (off := 59924) (ptr := 12) (word := word) mapped bound)

private theorem threadSpanStoreSteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : ModuleInst} {address : Nat} {mem : MemInst}
    (mapped : s.mem? (setupFrame m 126112 65536) ⟨0⟩ = some (address, mem))
    (bound : 59324 ≤ mem.bytes.size) :
    Steps P host ⟨s, setupFrame m 126112 65536, expression recordSpan⟩
      ⟨s.setMem address (writeWord mem 59320 65536), setupFrame m 126112 65536, []⟩ := by
  let f := setupFrame m 126112 65536
  have get : Step P host ⟨s, f, [.plain (.localGet ⟨1⟩)]⟩ ⟨s, f, [constI32 65536]⟩ :=
    .variable (.localGet (x := ⟨1⟩) (v := .i32 65536) rfl)
  have compare : Step P host ⟨s, f,
      expression [i32 65536, i32 8388608, .intRelOp .i32 (.lt .unsigned)]⟩
      ⟨s, f, [constI32 1]⟩ :=
    .numeric (.intRelOp (t := .i32) (op := .lt .unsigned) (x := 65536) (y := 8388608))
  have choose : Step P host ⟨s, f, expression [i32 65536, i32 8388608, i32 1, .select none]⟩
      ⟨s, f, [constI32 65536]⟩ :=
    .parametric (.selectTrue (v₁ := .i32 65536) (v₂ := .i32 8388608) (by decide))
  refine (get.steps.ctxtInstrs (vs := [.i32 0]) (rest := expression
    [i32 8388608, .localGet ⟨1⟩, i32 8388608, .intRelOp .i32 (.lt .unsigned), .select none,
      store 59320])).trans ?_
  refine (get.steps.ctxtInstrs (vs := [.i32 0, .i32 65536, .i32 8388608]) (rest := expression
    [i32 8388608, .intRelOp .i32 (.lt .unsigned), .select none, store 59320])).trans ?_
  refine (compare.steps.ctxtInstrs (vs := [.i32 0, .i32 65536, .i32 8388608]) (rest := expression
    [.select none, store 59320])).trans ?_
  exact (choose.steps.ctxtInstrs (vs := [.i32 0]) (rest := expression [store 59320])).tail
    (writeWord_step (off := 59320) (ptr := 0) (word := 65536) mapped bound)

/-- The selected reactor setup updates eight i32 words in the resolved memory. -/
def threadSetupMemory (mem : MemInst) (copiedWord : BitVec 32) : MemInst :=
  let writes : List (Nat × BitVec 32) :=
    [(59924, 59924), (59980, 0), (59976, 65536), (59972, 126112), (59932, 59924),
      (59928, 59924), (59936, copiedWord), (59320, 65536)]
  writes.foldl (fun current (offset, word) =>
    { current with bytes := Memory.writeSlice current.bytes offset (Memory.encodeLE 4 word.toNat) }) mem

theorem threadSetupSignature : sqlite.functionSignature? ⟨1516⟩ = some ⟨[], []⟩ := rfl

private theorem threadBodyReturns {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : ModuleInst} {address : Nat} {mem : MemInst} {word : BitVec 32}
    (mapped : s.mem? (Frame.forCall m [] threadSetupFunction.locals) ⟨0⟩ = some (address, mem))
    (bound : 59984 ≤ mem.bytes.size)
    (loaded : Memory.load mem.bytes 59892 4 = some word) :
    Steps P host ⟨s, Frame.forCall m [] threadSetupFunction.locals, expression threadSetupFunction.body⟩
      ⟨s.setMem address (threadSetupMemory mem word), setupFrame m 126112 65536, []⟩ := by
  let f := setupFrame m 126112 65536
  let first := writeWord mem 59924 59924
  let fields := threadFieldsMemory first
  let copied := writeWord fields 59936 word
  have firstBound : 59984 ≤ first.bytes.size := by
    rw [writeWord_size mem 59924 59924 (by omega)]
    exact bound
  have within : ∀ p ∈ prefixWrites, 59896 ≤ p.1 ∧ p.1 + 4 ≤ mem.bytes.size := by
    intro p hp
    simp [prefixWrites] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩
  obtain ⟨fieldsSize, fieldsLoad⟩ := applyWrites_preserve mem prefixWrites within
  change fields.bytes.size = mem.bytes.size at fieldsSize
  change Memory.load fields.bytes 59892 4 = Memory.load mem.bytes 59892 4 at fieldsLoad
  have fieldsBound : 59940 ≤ fields.bytes.size := by omega
  have copiedBound : 59324 ≤ copied.bytes.size := by
    rw [writeWord_size fields 59936 word fieldsBound]
    omega
  have runPrefix := threadPrefixSteps (P := P) (host := host) mapped (by omega)
  have fill : Steps P host ⟨s.setMem address first, f, expression threadFields⟩
      ⟨s.setMem address fields, f, []⟩ := by
    have run := threadFieldsSteps (P := P) (host := host)
      (mapped_after_write (mem' := first) rfl mapped) firstBound
    rw [setMem_twice] at run
    exact run
  have copy : Steps P host ⟨s.setMem address fields, f, expression copyField⟩
      ⟨s.setMem address copied, f, []⟩ := by
    have run := threadCopySteps (P := P) (host := host) (f := f)
      (mapped_after_write rfl mapped) fieldsBound (fieldsLoad.trans loaded)
    rw [setMem_twice] at run
    exact run
  have span : Steps P host ⟨s.setMem address copied, f, expression recordSpan⟩
      ⟨s.setMem address (threadSetupMemory mem word), f, []⟩ := by
    have run := threadSpanStoreSteps (P := P) (host := host) (m := m)
      (mapped_after_write (mem' := copied) rfl mapped) copiedBound
    rw [setMem_twice] at run
    exact run
  rw [actualBody]
  change Steps P host ⟨s, _, expression threadPrefix ++
    (expression threadFields ++ expression copyField) ++ expression recordSpan⟩ _
  simp only [List.append_assoc]
  refine (runPrefix.ctxtInstrs (vs := []) (rest := _)).trans ?_
  refine (fill.ctxtInstrs (vs := []) (rest := _)).trans ?_
  exact (copy.ctxtInstrs (vs := []) (rest := _)).trans span

/-- With the runtime slot linked and the callee memory covering the eight writes, the setup call
returns no values and restores the caller. The loaded word is obtained from the initial memory. -/
theorem threadSetupReturns {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {functionAddress memoryAddress : Nat} {fi : FuncInst H}
    {mem : MemInst} (slot : caller.module.funcs[1516]? = some functionAddress)
    (entry : s.funcs[functionAddress]? = some fi) (code : fi.code = .wasm threadSetupFunction)
    (signature : Expand fi.type (.func .nil .nil))
    (mapped : s.mem? (Frame.forCall fi.module [] threadSetupFunction.locals) ⟨0⟩ =
      some (memoryAddress, mem))
    (bound : 59984 ≤ mem.bytes.size) :
    ∃ word : BitVec 32, Memory.load mem.bytes 59892 4 = some word ∧
      Steps P host ⟨s, caller, [.plain (.call ⟨1516⟩)]⟩
        ⟨s.setMem memoryAddress (threadSetupMemory mem word), caller, []⟩ := by
  let word := BitVec.ofNat 32 (Memory.decodeLE (mem.bytes.extract 59892 59896))
  have loaded : Memory.load mem.bytes 59892 4 = some word := by
    unfold Memory.load Memory.readBytes
    rw [ite_eq_left (show 59892 + 4 ≤ mem.bytes.size by omega)]
    rfl
  refine ⟨word, loaded, ?_⟩
  let doneFrame := setupFrame fi.module 126112 65536
  let doneStore := s.setMem memoryAddress (threadSetupMemory mem word)
  have lookup := Step.call (P := P) (host := host) (x := ⟨1516⟩) slot entry
  have enter := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType fi.type) (vs := []) trivial entry signature rfl code
  have body := threadBodyReturns (P := P) (host := host) mapped bound loaded
  have inLabel := body.label (n := 0) (cont := [])
  have exitLabel : Step P host ⟨doneStore, doneFrame, [.label 0 [] []]⟩ ⟨doneStore, doneFrame, []⟩ :=
    Step.labelVals (vs := [])
  have finishBody : Steps P host ⟨s, _, [.label 0 [] (expression threadSetupFunction.body)]⟩
      ⟨doneStore, doneFrame, []⟩ := inLabel.tail exitLabel
  have leave : Step P host ⟨doneStore, caller, [.frame 0 doneFrame []]⟩ ⟨doneStore, caller, []⟩ :=
    Step.frameVals (vs := []) rfl
  exact ((lookup.steps.tail enter).trans (finishBody.frame (f := caller) (n := 0))).tail leave

end SqliteWasm
