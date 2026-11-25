module

public import SqliteWasm.WholeModule
public import SqliteWasmArtifactEntries
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CGlobalType)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536
set_option maxHeartbeats 300000

def initializerFunction : Func := (definedFunction? sqlite 25).get rfl

private def flagAddressCode : List Instr :=
  [.globalGet ⟨1⟩, .intConst .i32 59328, .intBinOp .i32 .add]

private def flagLoad : Instr := .intLoad .i32 none ⟨0⟩ ⟨2, 0⟩
private def flagTest : Instr := .intTestOp .i32 .eqz
private def guardTail : List Instr := [.brIf ⟨0⟩, .unreachable]

private def flagCheck : Instr :=
  .block .empty (flagAddressCode ++ [flagLoad, flagTest] ++ guardTail)

private def flagWrite : List Instr :=
  flagAddressCode ++ [.intConst .i32 1, .intStore .i32 none ⟨0⟩ ⟨2, 0⟩]

private def remainingCalls : List Instr := [.call ⟨1516⟩, .call ⟨23⟩]

private theorem initializerBody :
    initializerFunction.body = flagCheck :: flagWrite ++ remainingCalls := rfl

theorem originalInitializerFunction :
    ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
      definedFunction? m 25) = some initializerFunction := by
  rw [originalDecode]
  rfl

private theorem flagAddressSteps {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {base : BitVec 32}
    {globalAddr : Nat} {globalType : CGlobalType}
    (mapped : s.global? f ⟨1⟩ = some (globalAddr, ⟨globalType, .i32 base⟩)) :
    Steps P host ⟨s, f, expression flagAddressCode⟩ ⟨s, f, [constI32 (base + 59328#32)]⟩ := by
  have get : Step P host ⟨s, f, [.plain (.globalGet ⟨1⟩)]⟩ ⟨s, f, [constI32 base]⟩ :=
    .variable (.globalGet mapped)
  have add : Step P host
      ⟨s, f, [constI32 base, constI32 59328, .plain (.intBinOp .i32 .add)]⟩
      ⟨s, f, [constI32 (base + 59328#32)]⟩ := .numeric (.intBinOp rfl)
  exact (get.steps.ctxtInstrs (vs := []) (rest :=
    [constI32 59328, .plain (.intBinOp .i32 .add)])).tail add

private theorem loadWordStep {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {ptr word : BitVec 32} {memoryAddr : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (memoryAddr, mem))
    (loaded : Memory.load mem.bytes ptr.toNat 4 = some word) :
    Step P host ⟨s, f, [constI32 ptr, .plain flagLoad]⟩ ⟨s, f, [constI32 word]⟩ := by
  have cast : word.setWidth 32 = word := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt word.isLt]
  have load : Memory.load mem.bytes (ptr.toNat + 0) 4 = some word := by
    rwa [Nat.add_zero]
  have step : Step P host ⟨s, f, [constI32 ptr, .plain flagLoad]⟩
      ⟨s, f, [constI32 (word.setWidth 32)]⟩ :=
    .memory (MemoryStep.loadIntVal (t := .i32) (arg := ⟨2, 0⟩)
      (a := .i32) (i := ptr) (c := word) mapped load)
  simpa only [cast] using step

private theorem storeOneStep {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {ptr : BitVec 32} {memoryAddr : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (memoryAddr, mem))
    (bound : ptr.toNat + 4 ≤ mem.bytes.size) :
    Step P host ⟨s, f, [constI32 ptr, constI32 1, .plain (.intStore .i32 none ⟨0⟩ ⟨2, 0⟩)]⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes ptr.toNat (Memory.encodeLE 4 1) }, f, []⟩ := by
  apply Step.memory
  refine MemoryStep.storeIntVal (t := .i32) (arg := ⟨2, 0⟩)
    (a := .i32) (i := ptr) (c := 1#32) mapped ?_
  change Memory.store mem.bytes (ptr.toNat + 0) (count := 4) 1 = _
  rw [Nat.add_zero, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bound]
  rfl

private theorem reachFlagBranch {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {base word : BitVec 32} {globalAddr memoryAddr : Nat}
    {globalType : CGlobalType} {mem : MemInst}
    (global : s.global? f ⟨1⟩ = some (globalAddr, ⟨globalType, .i32 base⟩))
    (mapped : s.mem? f ⟨0⟩ = some (memoryAddr, mem))
    (loaded : Memory.load mem.bytes (base + 59328#32).toNat 4 = some word) :
    Steps P host ⟨s, f, expression [flagCheck]⟩
      ⟨s, f, [.label 0 []
        (constI32 (Numerics.intTestOp .i32 .eqz word) :: expression guardTail)]⟩ := by
  let code := expression flagAddressCode ++ [.plain flagLoad, .plain flagTest] ++ expression guardTail
  have enter : Step P host ⟨s, f, expression [flagCheck]⟩ ⟨s, f, [.label 0 [] code]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have test : Step P host ⟨s, f, [constI32 word, .plain flagTest]⟩
      ⟨s, f, [constI32 (Numerics.intTestOp .i32 .eqz word)]⟩ :=
    .numeric (.intTestOp (t := .i32) (op := .eqz) (x := word))
  have inside : Steps P host ⟨s, f, code⟩
      ⟨s, f, constI32 (Numerics.intTestOp .i32 .eqz word) :: expression guardTail⟩ := by
    change Steps P host ⟨s, f, expression flagAddressCode ++
      (.plain flagLoad :: .plain flagTest :: expression guardTail)⟩ _
    refine ((flagAddressSteps global).ctxtInstrs (vs := []) (rest := _)).trans ?_
    refine ((loadWordStep mapped loaded).steps.ctxtInstrs (vs := []) (rest := _)).trans ?_
    exact test.steps.ctxtInstrs (vs := []) (rest := expression guardTail)
  exact enter.steps.trans (inside.label (n := 0) (cont := []))

private theorem flagCheckZero {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {base : BitVec 32} {globalAddr memoryAddr : Nat}
    {globalType : CGlobalType} {mem : MemInst}
    (global : s.global? f ⟨1⟩ = some (globalAddr, ⟨globalType, .i32 base⟩))
    (mapped : s.mem? f ⟨0⟩ = some (memoryAddr, mem))
    (zero : Memory.load mem.bytes (base + 59328#32).toNat 4 = some 0) :
    Steps P host ⟨s, f, expression [flagCheck]⟩ ⟨s, f, []⟩ := by
  have branch : Step P host ⟨s, f, [constI32 1, .plain (.brIf ⟨0⟩)]⟩
      ⟨s, f, [.plain (.br ⟨0⟩)]⟩ := Step.brIfTrue (by decide)
  have exit : Step P host ⟨s, f, [.label 0 [] (expression [.br ⟨0⟩, .unreachable])]⟩
      ⟨s, f, []⟩ := Step.brLabelZero (vs' := []) (vs := []) rfl rfl
  have inside := (branch.steps.ctxtInstrs (vs := []) (rest := [.plain .unreachable])).label
    (n := 0) (cont := [])
  exact ((reachFlagBranch global mapped zero).trans inside).tail exit

/-- The zero flag lets the original initializer mark the word and reach its two calls. -/
theorem initializerZeroFlag {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {base : BitVec 32} {globalAddr memoryAddr : Nat}
    {globalType : CGlobalType} {mem : MemInst}
    (global : s.global? f ⟨1⟩ = some (globalAddr, ⟨globalType, .i32 base⟩))
    (mapped : s.mem? f ⟨0⟩ = some (memoryAddr, mem))
    (zero : Memory.load mem.bytes (base + 59328#32).toNat 4 = some 0) :
    Steps P host ⟨s, f, expression initializerFunction.body⟩
      ⟨s.setMem memoryAddr
        { mem with bytes := Memory.writeSlice mem.bytes (base + 59328#32).toNat (Memory.encodeLE 4 1) },
        f, expression [.call ⟨1516⟩, .call ⟨23⟩]⟩ := by
  let address := base + 59328#32
  let bytes := Memory.writeSlice mem.bytes address.toNat (Memory.encodeLE 4 1)
  have bound : address.toNat + 4 ≤ mem.bytes.size := by
    by_contra! out
    unfold Memory.load Memory.readBytes at zero
    rw [ite_eq_right (show ¬ address.toNat + 4 ≤ mem.bytes.size by omega)] at zero
    cases zero
  have store : Step P host ⟨s, f,
      [constI32 address, constI32 1, .plain (.intStore .i32 none ⟨0⟩ ⟨2, 0⟩)]⟩
      ⟨s.setMem memoryAddr { mem with bytes := bytes }, f, []⟩ := storeOneStep mapped bound
  have write : Steps P host ⟨s, f, expression flagWrite⟩
      ⟨s.setMem memoryAddr { mem with bytes := bytes }, f, []⟩ :=
    ((flagAddressSteps global).ctxtInstrs (vs := []) (rest :=
      expression [.intConst .i32 1, .intStore .i32 none ⟨0⟩ ⟨2, 0⟩])).tail store
  rw [initializerBody]
  change Steps P host ⟨s, f, expression [flagCheck] ++ expression flagWrite ++ expression remainingCalls⟩ _
  rw [List.append_assoc]
  exact ((flagCheckZero global mapped zero).ctxtInstrs (vs := [])
    (rest := expression flagWrite ++ expression remainingCalls)).trans
    (write.ctxtInstrs (vs := []) (rest := expression remainingCalls))

/-- A successfully loaded nonzero flag takes the original unreachable branch before any write. -/
theorem initializerNonzeroFlag {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {base word : BitVec 32} {globalAddr memoryAddr : Nat}
    {globalType : CGlobalType} {mem : MemInst}
    (global : s.global? f ⟨1⟩ = some (globalAddr, ⟨globalType, .i32 base⟩))
    (mapped : s.mem? f ⟨0⟩ = some (memoryAddr, mem))
    (loaded : Memory.load mem.bytes (base + 59328#32).toNat 4 = some word)
    (nonzero : word ≠ 0) :
    Steps P host ⟨s, f, expression initializerFunction.body⟩ ⟨s, f, [.trap]⟩ := by
  have branch := reachFlagBranch (P := P) (host := host) global mapped loaded
  have test : Numerics.intTestOp .i32 .eqz word = 0 := by
    have unequal : (word == (0 : BitVec 32)) = false := beq_eq_false_iff_ne.mpr nonzero
    change Numerics.bool32 (word == (0 : BitVec 32)) = 0
    rw [unequal]
    rfl
  rw [test] at branch
  have falseBranch : Step P host ⟨s, f, [constI32 0, .plain (.brIf ⟨0⟩)]⟩ ⟨s, f, []⟩ :=
    Step.brIfFalse
  have trap : Step P host ⟨s, f, [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩ :=
    .parametric .unreachable
  have fallthrough : Steps P host ⟨s, f, constI32 0 :: expression guardTail⟩
      ⟨s, f, [.trap]⟩ :=
    (falseBranch.steps.ctxtInstrs (vs := []) (rest := [.plain .unreachable])).tail trap
  have inner := fallthrough.label (n := 0) (cont := [])
  have trapped : Steps P host ⟨s, f, expression [flagCheck]⟩ ⟨s, f, [.trap]⟩ :=
    (branch.trans inner).tail (Step.trapLabel (n := 0) (cont := []))
  let rest := expression (flagWrite ++ remainingCalls)
  have dropRest : Step P host ⟨s, f, .trap :: rest⟩ ⟨s, f, [.trap]⟩ :=
    Step.trapInstrs (vs := []) (rest := rest) (Or.inr (by simp [rest, flagWrite, flagAddressCode, expression]))
  rw [initializerBody]
  exact (trapped.ctxtInstrs (vs := []) (rest := rest)).tail dropRest

end SqliteWasm
