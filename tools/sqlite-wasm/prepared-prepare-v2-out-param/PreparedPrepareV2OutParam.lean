module

public import SqliteWasm.PreparedPrepareV2Entry
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CGlobalType liftVal)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private def helper : Func := (definedFunction? sqlite 105).get (by kernel_rfl)
private def stackGlobal : Global := sqlite.globals[0]'(by decide)

private def prologue : List Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 16, .intBinOp .i32 .sub, .localTee ⟨7⟩,
    .globalSet ⟨0⟩, .localGet ⟨5⟩, .intConst .i32 0, .intStore .i32 none ⟨0⟩ ⟨2, 0⟩]

private theorem helperBody : helper.body = prologue ++ helper.body.drop 8 := by
  kernel_rfl

private theorem advance {P : Profile} {host : HostSemantics Nat}
    {s s' : Store Nat} {f f' : Frame} {head next rest : List Admin} {finish : Config Nat}
    (operands : List Val) (step : Step P host ⟨s, f, head⟩ ⟨s', f', next⟩)
    (tail : Steps P host ⟨s', f', vals operands ++ next ++ rest⟩ finish) :
    Steps P host ⟨s, f, vals operands ++ head ++ rest⟩ finish :=
  (step.steps.ctxtInstrs (vs := operands) (rest := rest)).trans tail

private theorem clearOutput {P : Profile} {host : HostSemantics Nat}
    {runtime : Store Nat} {mi : ModuleInst} {stack memory : Nat} {mem : MemInst}
    (db sql nByte stmtOut tailOut : BitVec 32)
    (stackMapped : runtime.global? { module := mi } ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩))
    (memMapped : runtime.mem? { module := mi } ⟨0⟩ = some (memory, mem))
    (bound : stmtOut.toNat + 4 ≤ mem.bytes.size) :
    let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    let start := Frame.forCall mi forwarded helper.locals
    let lowered := runtime.setGlobal stack (.i32 126096)
    let cleared := Memory.writeSlice mem.bytes stmtOut.toNat (Memory.encodeLE 4 0)
    Steps P host ⟨runtime, start, expression helper.body⟩
      ⟨lowered.setMem memory { mem with bytes := cleared },
        start.setLocal ⟨7⟩ (.i32 126096), expression (helper.body.drop 8)⟩ := by
  let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
    .i32 stmtOut, .i32 tailOut]
  let start := Frame.forCall mi forwarded helper.locals
  let withStack := start.setLocal ⟨7⟩ (.i32 126096)
  let lowered := runtime.setGlobal stack (.i32 126096)
  let cleared := Memory.writeSlice mem.bytes stmtOut.toNat (Memory.encodeLE 4 0)
  have getStack : runtime.global? start ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) := stackMapped
  have setStack : runtime.global? withStack ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) := stackMapped
  have mapped : lowered.mem? withStack ⟨0⟩ = some (memory, mem) := memMapped
  have zero : Step P host
      ⟨lowered, withStack, [constI32 stmtOut, constI32 0,
        .plain (.intStore .i32 none ⟨0⟩ ⟨2, 0⟩)]⟩
      ⟨lowered.setMem memory { mem with bytes := cleared }, withStack, []⟩ := by
    apply Step.memory
    refine MemoryStep.storeIntVal (t := .i32) (arg := ⟨2, 0⟩)
      (a := .i32) (i := stmtOut) (c := 0#32) mapped ?_
    change Memory.store mem.bytes (stmtOut.toNat + 0) (count := 4) 0 = _
    rw [Nat.add_zero, Memory.store, Memory.writeBytes, Memory.encodeLE_size, ite_eq_left bound]
    rfl
  have run : Steps P host ⟨runtime, start, expression prologue⟩
      ⟨lowered.setMem memory { mem with bytes := cleared }, withStack, []⟩ := by
    unfold prologue expression
    refine advance [] (.variable (.globalGet getStack)) ?_
    refine advance [] (head := [constI32 126112, constI32 16, .plain (.intBinOp .i32 .sub)])
      (.numeric (.intBinOp (t := .i32) (op := .sub) (x := 126112) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 126096, .plain (.localTee ⟨7⟩)])
      (.variable (.localTee (x := ⟨7⟩) (v := .i32 126096))) ?_
    refine advance [.i32 126096] (head := [constI32 126096, .plain (.localSet ⟨7⟩)])
      (.variable (.localSet (f := start) (x := ⟨7⟩) (v := .i32 126096)
        (show 7 < 11 by decide))) ?_
    refine advance [] (head := [constI32 126096, .plain (.globalSet ⟨0⟩)])
      (.variable (.globalSet (v := .i32 126096) setStack)) ?_
    refine advance [] (head := [.plain (.localGet ⟨5⟩)]) (.variable (.localGet (x := ⟨5⟩) (v := .i32 stmtOut)
      (f := withStack) rfl)) ?_
    exact zero.steps
  change Steps P host ⟨runtime, start, expression helper.body⟩ _
  have source : expression helper.body = expression prologue ++ expression (helper.body.drop 8) := by
    conv_lhs => rw [helperBody]
    exact List.map_append
  rw [source]
  exact run.ctxtInstrs (vs := []) (rest := expression (helper.body.drop 8))

/-- With four bytes in bounds at the statement-output address, the named wrapper
and the actual helper's prologue lower the stack pointer and zero that output.
Execution stops with the rest of the helper pending in its original call context. -/
theorem reactorPreparedPrepareV2ClearsOutput (P : Profile) (host : HostSemantics Nat)
    (db sql nByte stmtOut tailOut : BitVec 32) (bound : stmtOut.toNat + 4 ≤ 131072) :
    let args : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    ∃ runtime frame address helperAddress wrapper code stack memory mem,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_prepare_v2") =
        some ⟨"sqlite3_prepare_v2", .func address⟩ ∧
      frame.module.funcs[113]? = some address ∧
      frame.module.funcs[105]? = some helperAddress ∧
      definedFunction? sqlite 113 = some wrapper ∧
      definedFunction? sqlite 105 = some code ∧
      runtime.global? frame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) ∧
      runtime.mem? frame ⟨0⟩ = some (memory, mem) ∧
      InvokeOk runtime address args ∧
      let lowered := runtime.setGlobal stack (.i32 126096)
      let cleared := Memory.writeSlice mem.bytes stmtOut.toNat (Memory.encodeLE 4 0)
      Steps P host (invoke runtime address args)
        ⟨lowered.setMem memory { mem with bytes := cleared }, {}, [
          .frame 1 (Frame.forCall frame.module args wrapper.locals) [.label 1 [] [
            .frame 1 ((Frame.forCall frame.module forwarded code.locals).setLocal ⟨7⟩ (.i32 126096))
              [.label 1 [] (expression (code.body.drop 8))]
          ]]
        ]⟩ := by
  obtain ⟨runtime, frame, address, helperAddress, wrapper, code, _, _, prepared,
      exported, slot, helperSlot, wrapperSource, helperSource, _, _, typed, entered⟩ :=
    reactorPreparedPrepareV2Entry P host db sql nByte stmtOut tailOut
  obtain ⟨before, allocated, sameRuntime, sameFrame, mem, samePrepared, alloc, _, _, _, mapped,
      size, _, _, globals⟩ := reactorDirectPreparationWithGlobals
  have identified := Option.some.inj (samePrepared.symm.trans prepared)
  obtain ⟨runtimeEq, frameAndStart⟩ := Prod.mk.inj identified
  obtain ⟨frameEq, _⟩ := Prod.mk.inj frameAndStart
  subst sameRuntime sameFrame
  have stack := Link.GC.Preparation.allocModule_global
    (as := List.range 23) (n := 0) (g := stackGlobal) (v := .i32 126112) alloc
    (by kernel_rfl) rfl
  have stackSlot : frame.module.globals[0]? = some before.globals.length := by
    simpa only [Nat.add_zero] using stack.1
  have stackType : (⟨stackGlobal.type.mutability,
      (liftVal stackGlobal.type.value).substAll ((allocTypes sqlite.types).map .dt)⟩ : CGlobalType) =
      ⟨.var, .i32⟩ := by kernel_rfl
  have stackEntry : runtime.globals[before.globals.length]? =
      some ⟨⟨.var, .i32⟩, .i32 126112⟩ := by
    rw [globals]
    simpa only [Nat.add_zero, stackType] using stack.2
  have stackMapped : runtime.global? frame ⟨0⟩ =
      some (before.globals.length, ⟨⟨.var, .i32⟩, .i32 126112⟩) := by
    change (frame.module.globals[0]?.bind fun a => runtime.globals[a]?.bind fun g => some (a, g)) = _
    rw [stackSlot, Option.bind_some, stackEntry]
    rfl
  have known : definedFunction? sqlite 105 = some helper := by kernel_rfl
  have sameHelper := Option.some.inj (helperSource.symm.trans known)
  subst code
  have fits : stmtOut.toNat + 4 ≤ mem.bytes.size := size.symm ▸ bound
  have run := clearOutput (P := P) (host := host) db sql nByte stmtOut tailOut
    (mi := frame.module) stackMapped mapped fits
  refine ⟨runtime, frame, address, helperAddress, wrapper, helper, before.globals.length,
    before.mems.length, mem, prepared, exported, slot, helperSlot, wrapperSource, known,
    stackMapped, mapped, typed, ?_⟩
  exact entered.trans ((((run.label (n := 1) (cont := [])).frame (n := 1)).label
    (n := 1) (cont := [])).frame (f := {}) (n := 1))

#print axioms reactorPreparedPrepareV2ClearsOutput

end SqliteWasm
