module

public import SqliteWasm.DirectPreparation
public import SqliteWasmArtifactEntries
import Silmaril.Wasm.Auto.Bridge.Thms
import Silmaril.Wasm.Auto.Equiv.Thms
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CGlobalType DefType Expand Ty liftVal)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private def logger : Func := (definedFunction? sqlite 26).get (by kernel_rfl)
private def loggerType : DefType := ((allocTypes sqlite.types)[logger.type.toNat]?).get (by kernel_rfl)
private def stackGlobal : Global := sqlite.globals[0]'(by decide)

private def prologue : List Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 752, .intBinOp .i32 .sub, .localTee ⟨3⟩, .globalSet ⟨0⟩]

private def callbackLoad : Instr := .intLoad .i32 none ⟨0⟩ ⟨2, 52996⟩

private def guard : List Instr :=
  [.intConst .i32 0, callbackLoad, .intTestOp .i32 .eqz, .brIf ⟨0⟩]

private def loggingCode : List Instr :=
  match logger.body[5]? with
  | some (Instr.block .empty body) => body.drop 4
  | _ => []

private def epilogue : List Instr :=
  [.localGet ⟨3⟩, .intConst .i32 752, .intBinOp .i32 .add, .globalSet ⟨0⟩]

private theorem loggerBody :
    logger.body = prologue ++ [.block .empty (guard ++ loggingCode)] ++ epilogue := by
  kernel_rfl

private theorem advance {H : Type} {P : Profile} {host : HostSemantics H}
    {s s' : Store H} {f f' : Frame} {head next rest : List Admin} {finish : Config H}
    (operands : List Val) (step : Step P host ⟨s, f, head⟩ ⟨s', f', next⟩)
    (tail : Steps P host ⟨s', f', vals operands ++ next ++ rest⟩ finish) :
    Steps P host ⟨s, f, vals operands ++ head ++ rest⟩ finish :=
  (step.steps.ctxtInstrs (vs := operands) (rest := rest)).trans tail

private theorem stackLookup {H : Type} {s : Store H} {f : Frame} {stack : Nat} {sp : BitVec 32}
    (slot : f.module.globals[0]? = some stack)
    (entry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 sp⟩) :
    s.global? f ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 sp⟩) := by
  change (f.module.globals[0]?.bind fun a => s.globals[a]?.bind fun g => some (a, g)) = _
  rw [slot, Option.bind_some, entry]
  rfl

private theorem skipLog {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {ma : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (ma, mem))
    (zero : Memory.load mem.bytes 52996 4 = some 0) :
    Steps P host ⟨s, f, expression [.block .empty (guard ++ loggingCode)]⟩ ⟨s, f, []⟩ := by
  have load : Step P host ⟨s, f, [constI32 0, .plain callbackLoad]⟩ ⟨s, f, [constI32 0]⟩ :=
    .memory (MemoryStep.loadIntVal (t := .i32) (arg := ⟨2, 52996⟩)
      (a := .i32) (i := 0) (c := 0) mapped zero)
  have branch : Steps P host ⟨s, f, expression (guard ++ loggingCode)⟩
      ⟨s, f, [.plain (.br ⟨0⟩)] ++ expression loggingCode⟩ := by
    refine advance [] load ?_
    refine advance [] (head := [constI32 0, .plain (.intTestOp .i32 .eqz)])
      (.numeric (.intTestOp (t := .i32) (op := .eqz) (x := 0))) ?_
    have step : Step P host ⟨s, f, [constI32 1, .plain (.brIf ⟨0⟩)]⟩
        ⟨s, f, [.plain (.br ⟨0⟩)]⟩ := Step.brIfTrue (by decide)
    exact step.steps.ctxtInstrs (vs := []) (rest := expression loggingCode)
  have enter : Step P host ⟨s, f, expression [.block .empty (guard ++ loggingCode)]⟩
      ⟨s, f, [.label 0 [] (expression (guard ++ loggingCode))]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  exact (enter.steps.trans (branch.label (n := 0) (cont := []))).tail
    (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)

private theorem loggerReturns {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {address stack ma : Nat} {mem : MemInst} {sp : BitVec 32}
    (err fmt fmtArgs : BitVec 32)
    (slot : caller.module.funcs[26]? = some address)
    (entry : s.funcs[address]? = some ⟨loggerType, caller.module, .wasm logger⟩)
    (stackSlot : caller.module.globals[0]? = some stack)
    (stackEntry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 sp⟩)
    (mapped : s.mem? caller ⟨0⟩ = some (ma, mem))
    (zero : Memory.load mem.bytes 52996 4 = some 0) :
    Steps P host ⟨s, caller, vals [.i32 err, .i32 fmt, .i32 fmtArgs] ++ [.plain (.call ⟨26⟩)]⟩
      ⟨s, caller, []⟩ := by
  let args : List Val := [.i32 err, .i32 fmt, .i32 fmtArgs]
  let f := Frame.forCall caller.module args logger.locals
  let loweredSP := sp - 752#32
  let loweredFrame := f.setLocal ⟨3⟩ (.i32 loweredSP)
  let loweredStore := s.setGlobal stack (.i32 loweredSP)
  have before : s.global? f ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 sp⟩) :=
    stackLookup stackSlot stackEntry
  have beforeSet : s.global? loweredFrame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 sp⟩) :=
    stackLookup stackSlot stackEntry
  have lower : Steps P host ⟨s, f, expression prologue⟩ ⟨loweredStore, loweredFrame, []⟩ := by
    unfold prologue expression
    refine advance [] (.variable (.globalGet before)) ?_
    refine advance [] (head := [constI32 sp, constI32 752, .plain (.intBinOp .i32 .sub)])
      (.numeric (.intBinOp (t := .i32) (op := .sub) (x := sp) (y := 752) rfl)) ?_
    refine advance [] (head := [constI32 loweredSP, .plain (.localTee ⟨3⟩)])
      (.variable (.localTee (x := ⟨3⟩) (v := .i32 loweredSP))) ?_
    refine advance [.i32 loweredSP] (head := [constI32 loweredSP, .plain (.localSet ⟨3⟩)])
      (.variable (.localSet (f := f) (x := ⟨3⟩) (v := .i32 loweredSP)
        (show 3 < 4 by decide))) ?_
    exact (Step.variable (.globalSet (v := .i32 loweredSP) beforeSet)).steps
  have bypass : Steps P host ⟨loweredStore, loweredFrame, expression [.block .empty (guard ++ loggingCode)]⟩
      ⟨loweredStore, loweredFrame, []⟩ := skipLog mapped zero
  have loweredEntry : loweredStore.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 loweredSP⟩ := by
    simp [loweredStore, Store.setGlobal, stackEntry]
  have after : loweredStore.global? loweredFrame ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 loweredSP⟩) := stackLookup stackSlot loweredEntry
  have restored : loweredStore.setGlobal stack (.i32 sp) = s := by
    change (s.setGlobal stack (.i32 loweredSP)).setGlobal stack (.i32 sp) = s
    rw [Silmaril.Wasm.Auto.Equiv.setGlobal_setGlobal]
    apply Silmaril.Wasm.Auto.Bridge.setGlobal_self
    rw [stackEntry]
    rfl
  have add : Step P host
      ⟨loweredStore, loweredFrame, [constI32 loweredSP, constI32 752, .plain (.intBinOp .i32 .add)]⟩
      ⟨loweredStore, loweredFrame, [constI32 sp]⟩ :=
    .numeric (.intBinOp (t := .i32) (op := .add) (x := loweredSP) (y := 752)
      (congrArg Except.ok (BitVec.sub_add_cancel sp 752)))
  have restore : Steps P host ⟨loweredStore, loweredFrame, expression epilogue⟩ ⟨s, loweredFrame, []⟩ := by
    unfold epilogue expression
    refine advance [] (head := [.plain (.localGet ⟨3⟩)])
      (.variable (.localGet (x := ⟨3⟩) (v := .i32 loweredSP) rfl)) ?_
    refine advance [] (head := [constI32 loweredSP, constI32 752, .plain (.intBinOp .i32 .add)]) add ?_
    rw [← restored]
    exact (Step.variable (.globalSet (v := .i32 sp) after)).steps
  have body : Steps P host ⟨s, f, expression logger.body⟩ ⟨s, loweredFrame, []⟩ := by
    simp only [loggerBody, expression, List.map_append]
    exact (lower.ctxtInstrs (vs := []) (rest := expression [.block .empty (guard ++ loggingCode)] ++
      expression epilogue)).trans ((bypass.ctxtInstrs (vs := []) (rest := expression epilogue)).trans restore)
  have signature : Expand loggerType (.func (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32 .nil))) .nil) :=
    Expand.iff.mpr (by kernel_rfl)
  have call := Step.call (P := P) (host := host) (f := caller) (x := ⟨26⟩) slot entry
  have enter := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType loggerType) (vs := args) trivial entry signature rfl rfl
  have inner : Steps P host ⟨s, f, [.label 0 [] (expression logger.body)]⟩ ⟨s, loweredFrame, []⟩ :=
    (body.label (n := 0) (cont := [])).tail (Step.labelVals (vs := []))
  exact ((call.steps.ctxtInstrs (vs := args) (rest := [])).tail enter).trans
    ((inner.frame (f := caller) (n := 0)).tail (Step.frameVals (vs := []) rfl))

/-- The pinned internal logging helper restores the whole store and caller
when its mapped callback word is zero. The stack arithmetic is modulo i32. -/
theorem reactorLogDisabledCall {H : Type} (P : Profile) (host : HostSemantics H)
    {s : Store H} {caller : Frame} {address stack ma : Nat} {mem : MemInst} {sp : BitVec 32}
    {fn : Func} {type : DefType}
    (err fmt fmtArgs : BitVec 32)
    (source : definedFunction? sqlite 26 = some fn)
    (allocatedType : (allocTypes sqlite.types)[fn.type.toNat]? = some type)
    (slot : caller.module.funcs[26]? = some address)
    (entry : s.funcs[address]? = some ⟨type, caller.module, .wasm fn⟩)
    (stackSlot : caller.module.globals[0]? = some stack)
    (stackEntry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 sp⟩)
    (mapped : s.mem? caller ⟨0⟩ = some (ma, mem))
    (zero : Memory.load mem.bytes 52996 4 = some 0) :
    Steps P host ⟨s, caller, vals [.i32 err, .i32 fmt, .i32 fmtArgs] ++ [.plain (.call ⟨26⟩)]⟩
      ⟨s, caller, []⟩ := by
  have knownSource : definedFunction? sqlite 26 = some logger := by kernel_rfl
  have sameFn := Option.some.inj (source.symm.trans knownSource)
  subst fn
  have knownType : (allocTypes sqlite.types)[logger.type.toNat]? = some loggerType := by kernel_rfl
  have sameType := Option.some.inj (allocatedType.symm.trans knownType)
  subst type
  exact loggerReturns err fmt fmtArgs slot entry stackSlot stackEntry mapped zero

/-- Direct preparation resolves the pinned logger and its stack and memory
entries. The callback-word premise refers to this exact mapped memory. -/
theorem reactorPreparedLogDisabled (P : Profile) (host : HostSemantics Nat)
    (err fmt fmtArgs : BitVec 32) :
    ∃ runtime frame address memory mem,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.funcs[26]? = some address ∧ runtime.mem? frame ⟨0⟩ = some (memory, mem) ∧
      (Memory.load mem.bytes 52996 4 = some 0 →
        Steps P host ⟨runtime, frame,
          vals [.i32 err, .i32 fmt, .i32 fmtArgs] ++ [.plain (.call ⟨26⟩)]⟩ ⟨runtime, frame, []⟩) := by
  obtain ⟨before, _, runtime, frame, mem, prepared, alloc, sameFunctions, _, _, mapped,
    _, _, _, sameGlobals⟩ := reactorDirectPreparationWithGlobals
  have logEntry := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 3) (fn := logger) (d := loggerType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have slot : frame.module.funcs[26]? = some (before.funcs.length + 3) := by
    simpa only [List.length_range] using logEntry.1
  have entry : runtime.funcs[before.funcs.length + 3]? =
      some ⟨loggerType, frame.module, .wasm logger⟩ := sameFunctions.symm ▸ logEntry.2
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
    rw [sameGlobals]
    simpa only [Nat.add_zero, stackType] using stack.2
  exact ⟨runtime, frame, before.funcs.length + 3, before.mems.length, mem, prepared, slot, mapped,
    loggerReturns err fmt fmtArgs slot entry stackSlot stackEntry mapped⟩

#print axioms reactorLogDisabledCall
#print axioms reactorPreparedLogDisabled

end SqliteWasm
