module

public import SqliteWasm.PreparedPrepareV2OutParam
public import SqliteWasm.PreparedNullDbCheck
import Silmaril.Wasm.Auto.Bridge.Thms
import Silmaril.Wasm.Auto.Equiv.Thms
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private def wrapperCode : Func := (definedFunction? sqlite 113).get (by kernel_rfl)
private def helper : Func := (definedFunction? sqlite 105).get (by kernel_rfl)
private def check : Func := (definedFunction? sqlite 130).get (by kernel_rfl)
private def logger : Func := (definedFunction? sqlite 26).get (by kernel_rfl)
private def wrapperType : DefType := ((allocTypes sqlite.types)[wrapperCode.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType := ((allocTypes sqlite.types)[helper.type.toNat]?).get (by kernel_rfl)
private def checkType : DefType := ((allocTypes sqlite.types)[check.type.toNat]?).get (by kernel_rfl)
private def loggerType : DefType := ((allocTypes sqlite.types)[logger.type.toNat]?).get (by kernel_rfl)

private def checkCode : List Instr := [.localGet ⟨0⟩, .call ⟨130⟩, .localSet ⟨8⟩]

private def sqlGuard : List Instr :=
  [.localGet ⟨1⟩, .intTestOp .i32 .eqz, .brIf ⟨0⟩, .localGet ⟨8⟩, .brIf ⟨1⟩]

private def diagnostic (offset : Fin (2 ^ 64)) (value : BitVec 32) : List Instr :=
  [.localGet ⟨7⟩, .intConst .i32 value, .intStore .i32 none ⟨0⟩ ⟨2, offset⟩]

private def reportCode : List Instr :=
  [.intConst .i32 21, .localSet ⟨8⟩, .intConst .i32 21, .intConst .i32 17113,
    .localGet ⟨7⟩, .call ⟨26⟩, .br ⟨1⟩]

private def rejection : List Instr :=
  [.block .empty sqlGuard] ++ diagnostic 8 19917 ++ diagnostic 4 149304 ++
    diagnostic 0 12389 ++ reportCode

private def remainder : List Instr :=
  match helper.body[11]? with
  | some (Instr.block .empty (_ :: rest)) => rest
  | _ => []

private def epilogue : List Instr :=
  [.localGet ⟨7⟩, .intConst .i32 16, .intBinOp .i32 .add, .globalSet ⟨0⟩, .localGet ⟨8⟩]

private theorem suffix :
    helper.body.drop 8 = checkCode ++ [.block .empty (.block .empty rejection :: remainder)] ++ epilogue := by
  kernel_rfl

/-- The writes of the named null-input rejection in execution order. -/
def prepareV2NullRejectionBytes (initial : ByteArray) (stmtOut : Nat) : ByteArray :=
  let cleared := Memory.writeSlice initial stmtOut (Memory.encodeLE 4 0)
  let checked := Memory.writeSlice cleared 126080 (Memory.encodeLE 4 18995)
  let high := Memory.writeSlice checked 126104 (Memory.encodeLE 4 19917)
  let middle := Memory.writeSlice high 126100 (Memory.encodeLE 4 149304)
  Memory.writeSlice middle 126096 (Memory.encodeLE 4 12389)

private theorem advance {P : Profile} {host : HostSemantics Nat}
    {s s' : Store Nat} {f f' : Frame} {head next rest : List Admin} {finish : Config Nat}
    (operands : List Val) (step : Step P host ⟨s, f, head⟩ ⟨s', f', next⟩)
    (tail : Steps P host ⟨s', f', vals operands ++ next ++ rest⟩ finish) :
    Steps P host ⟨s, f, vals operands ++ head ++ rest⟩ finish :=
  (step.steps.ctxtInstrs (vs := operands) (rest := rest)).trans tail

private theorem enterBlock {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {f : Frame} {code : List Instr} :
    Step P host ⟨s, f, expression [.block .empty code]⟩ ⟨s, f, [.label 0 [] (expression code)]⟩ :=
  Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl

private theorem wordWrite (bytes : ByteArray) (address value : Nat)
    (fits : address + 4 ≤ bytes.size) :
    Memory.writeBytes bytes address (Memory.encodeLE 4 value) =
      some (Memory.writeSlice bytes address (Memory.encodeLE 4 value)) := by
  rw [Memory.writeBytes, Memory.encodeLE_size, ite_eq_left fits]

private theorem wordRead {bytes : ByteArray} {address value readAt : Nat}
    (fits : address + 4 ≤ bytes.size)
    (separate : readAt + 4 ≤ address ∨ address + 4 ≤ readAt) :
    Memory.load (Memory.writeSlice bytes address (Memory.encodeLE 4 value)) readAt 4 =
      Memory.load bytes readAt 4 := by
  unfold Memory.load
  rw [Memory.readBytes_writeBytes_disjoint _ _ _ _ _ _ (wordWrite bytes address value fits)
    (by simpa only [Memory.encodeLE_size] using separate)]

private theorem wordFacts {bytes : ByteArray} {address value : Nat}
    (fits : address + 4 ≤ bytes.size)
    (separate : 53000 ≤ address ∨ address + 4 ≤ 52996)
    (zero : Memory.load bytes 52996 4 = some 0) :
    let updated := Memory.writeSlice bytes address (Memory.encodeLE 4 value)
    updated.size = bytes.size ∧ Memory.load updated 52996 4 = some 0 := by
  have write := wordWrite bytes address value fits
  refine ⟨Memory.writeBytes_size _ _ _ _ write, ?_⟩
  exact (wordRead fits separate).trans zero

private theorem mappedAfterWrite {s : Store Nat} {f : Frame} {memory : Nat}
    {old new : MemInst} (slot : f.module.mems[0]? = some memory)
    (entry : s.mems[memory]? = some old) :
    (s.setMem memory new).mem? f ⟨0⟩ = some (memory, new) := by
  have index := (List.getElem?_eq_some_iff.mp entry).1
  change (f.module.mems[0]?.bind fun a =>
    (s.mems.set memory new)[a]?.bind fun m => some (a, m)) = _
  rw [slot, Option.bind_some, List.getElem?_set_self index]
  rfl

private theorem writeDiagnostic {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {f : Frame} {memory : Nat} {mem : MemInst}
    (offset : Fin (2 ^ 64)) (value : BitVec 32)
    (localStack : f.local? ⟨7⟩ = some (some (.i32 126096)))
    (mapped : s.mem? f ⟨0⟩ = some (memory, mem))
    (fits : 126096 + offset.val + 4 ≤ mem.bytes.size) :
    let bytes := Memory.writeSlice mem.bytes (126096 + offset.val) (Memory.encodeLE 4 value.toNat)
    Steps P host ⟨s, f, expression (diagnostic offset value)⟩
      ⟨s.setMem memory { mem with bytes }, f, []⟩ := by
  refine advance [] (.variable (.localGet localStack)) ?_
  apply Step.steps
  apply Step.memory
  exact MemoryStep.storeIntVal (t := .i32) (arg := ⟨2, offset⟩)
    (a := .i32) (i := 126096) (c := value) mapped (wordWrite _ _ _ fits)

private theorem skipSqlGuard {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {f : Frame} (sql : f.local? ⟨1⟩ = some (some (.i32 0))) :
    Steps P host ⟨s, f, expression [.block .empty sqlGuard]⟩ ⟨s, f, []⟩ := by
  have taken : Steps P host ⟨s, f, expression sqlGuard⟩
      ⟨s, f, [.plain (.br ⟨0⟩)] ++ expression [.localGet ⟨8⟩, .brIf ⟨1⟩]⟩ := by
    refine advance [] (.variable (.localGet sql)) ?_
    refine advance [] (head := [constI32 0, .plain (.intTestOp .i32 .eqz)])
      (.numeric (.intTestOp (t := .i32) (op := .eqz) (x := 0))) ?_
    have branch : Step P host ⟨s, f, [constI32 1, .plain (.brIf ⟨0⟩)]⟩
        ⟨s, f, [.plain (.br ⟨0⟩)]⟩ := Step.brIfTrue (by decide)
    exact branch.steps.ctxtInstrs (vs := []) (rest := expression [.localGet ⟨8⟩, .brIf ⟨1⟩])
  exact (enterBlock.steps.trans (taken.label (n := 0) (cont := []))).tail
    (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)

private theorem rejectSuffix (P : Profile) (host : HostSemantics Nat)
    {s : Store Nat} {mi : ModuleInst} {checkAddr logAddr stack memory : Nat} {mem : MemInst}
    (nByte stmtOut tailOut : BitVec 32)
    (checkSlot : mi.funcs[130]? = some checkAddr)
    (checkEntry : s.funcs[checkAddr]? = some ⟨checkType, mi, .wasm check⟩)
    (logSlot : mi.funcs[26]? = some logAddr)
    (logEntry : s.funcs[logAddr]? = some ⟨loggerType, mi, .wasm logger⟩)
    (stackSlot : mi.globals[0]? = some stack)
    (stackEntry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126112⟩)
    (memorySlot : mi.mems[0]? = some memory)
    (memoryEntry : s.mems[memory]? = some mem)
    (fits : stmtOut.toNat + 4 ≤ mem.bytes.size)
    (scratchFits : 126108 ≤ mem.bytes.size)
    (separate : 53000 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 52996)
    (outCheckScratch : 126084 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 126080)
    (outReportScratch : 126108 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 126096)
    (zero : Memory.load mem.bytes 52996 4 = some 0) :
    let forwarded : List Val := [.i32 0, .i32 0, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    let f := (Frame.forCall mi forwarded helper.locals).setLocal ⟨7⟩ (.i32 126096)
    let cleared := Memory.writeSlice mem.bytes stmtOut.toNat (Memory.encodeLE 4 0)
    Memory.load (prepareV2NullRejectionBytes mem.bytes stmtOut.toNat) stmtOut.toNat 4 = some 0 ∧
    ∃ finish,
      Steps P host ⟨(s.setGlobal stack (.i32 126096)).setMem memory { mem with bytes := cleared },
        f, expression (helper.body.drop 8)⟩
        ⟨s.setMem memory { mem with bytes := prepareV2NullRejectionBytes mem.bytes stmtOut.toNat },
          finish, [constI32 21]⟩ := by
  let forwarded : List Val := [.i32 0, .i32 0, .i32 nByte, .i32 128, .i32 0,
    .i32 stmtOut, .i32 tailOut]
  let f := (Frame.forCall mi forwarded helper.locals).setLocal ⟨7⟩ (.i32 126096)
  let checkedFrame := f.setLocal ⟨8⟩ (.i32 0)
  let finish := checkedFrame.setLocal ⟨8⟩ (.i32 21)
  let lowered := s.setGlobal stack (.i32 126096)
  let atBytes (bytes : ByteArray) := lowered.setMem memory { mem with bytes }
  let cleared := Memory.writeSlice mem.bytes stmtOut.toNat (Memory.encodeLE 4 0)
  let checked := Memory.writeSlice cleared 126080 (Memory.encodeLE 4 18995)
  let high := Memory.writeSlice checked 126104 (Memory.encodeLE 4 19917)
  let middle := Memory.writeSlice high 126100 (Memory.encodeLE 4 149304)
  let final := Memory.writeSlice middle 126096 (Memory.encodeLE 4 12389)
  let output := s.setMem memory { mem with bytes := final }
  have setAgain (old new : ByteArray) : (atBytes old).setMem memory { mem with bytes := new } =
      atBytes new := by
    simp [atBytes, Store.setMem, List.set_set]
  have entryAtBytes (bytes : ByteArray) :
      (atBytes bytes).mems[memory]? = some { mem with bytes } := by
    have index := (List.getElem?_eq_some_iff.mp memoryEntry).1
    change (s.mems.set memory { mem with bytes })[memory]? = _
    rw [List.getElem?_set_self index]
  have mapped (bytes : ByteArray) :
      (atBytes bytes).mem? checkedFrame ⟨0⟩ = some (memory, { mem with bytes }) :=
    mappedAfterWrite memorySlot memoryEntry
  have stackLow : lowered.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126096⟩ := by
    simp [lowered, Store.setGlobal, stackEntry]
  have clearedFacts : cleared.size = mem.bytes.size ∧ Memory.load cleared 52996 4 = some 0 :=
    wordFacts (value := 0) fits separate zero
  have checkedFacts : checked.size = cleared.size ∧ Memory.load checked 52996 4 = some 0 :=
    wordFacts (address := 126080) (value := 18995) (by rw [clearedFacts.1]; omega)
      (Or.inl (by decide)) clearedFacts.2
  have highFacts : high.size = checked.size ∧ Memory.load high 52996 4 = some 0 :=
    wordFacts (address := 126104) (value := 19917) (by rw [checkedFacts.1, clearedFacts.1]; omega)
      (Or.inl (by decide)) checkedFacts.2
  have middleFacts : middle.size = high.size ∧ Memory.load middle 52996 4 = some 0 :=
    wordFacts (address := 126100) (value := 149304)
      (by rw [highFacts.1, checkedFacts.1, clearedFacts.1]; omega)
      (Or.inl (by decide)) highFacts.2
  have finalFacts : final.size = middle.size ∧ Memory.load final 52996 4 = some 0 :=
    wordFacts (address := 126096) (value := 12389)
      (by rw [middleFacts.1, highFacts.1, checkedFacts.1, clearedFacts.1]; omega)
      (Or.inl (by decide)) middleFacts.2
  have clearedOut : Memory.load cleared stmtOut.toNat 4 = some 0 := by
    have read := Memory.readBytes_writeBytes _ _ _ _ (wordWrite mem.bytes stmtOut.toNat 0 fits)
    rw [Memory.encodeLE_size] at read
    unfold Memory.load
    rw [read]
    rfl
  have checkedOut : Memory.load checked stmtOut.toNat 4 = some 0 :=
    (wordRead (address := 126080) (value := 18995) (by rw [clearedFacts.1]; omega)
      (by omega)).trans clearedOut
  have highOut : Memory.load high stmtOut.toNat 4 = some 0 :=
    (wordRead (address := 126104) (value := 19917)
      (by rw [checkedFacts.1, clearedFacts.1]; omega) (by omega)).trans checkedOut
  have middleOut : Memory.load middle stmtOut.toNat 4 = some 0 :=
    (wordRead (address := 126100) (value := 149304)
      (by rw [highFacts.1, checkedFacts.1, clearedFacts.1]; omega) (by omega)).trans highOut
  have finalOut : Memory.load final stmtOut.toNat 4 = some 0 :=
    (wordRead (address := 126096) (value := 12389)
      (by rw [middleFacts.1, highFacts.1, checkedFacts.1, clearedFacts.1]; omega) (by omega)).trans middleOut
  have checkSource : definedFunction? sqlite 130 = some check := by kernel_rfl
  have checkSig : (allocTypes sqlite.types)[check.type.toNat]? = some checkType := by kernel_rfl
  have logSource : definedFunction? sqlite 26 = some logger := by kernel_rfl
  have logSig : (allocTypes sqlite.types)[logger.type.toNat]? = some loggerType := by kernel_rfl
  have checkRun : Steps P host ⟨atBytes cleared, f, [constI32 0, .plain (.call ⟨130⟩)]⟩
      ⟨atBytes checked, f, [constI32 0]⟩ := by
    have run := reactorNullDbCheck P host (s := atBytes cleared) (caller := f) (sp := 126096)
      checkSource checkSig checkSlot checkEntry logSource logSig logSlot logEntry stackSlot stackLow
      memorySlot (entryAtBytes cleared) (by change 126084 ≤ cleared.size; rw [clearedFacts.1]; omega)
      (Or.inl (by decide)) clearedFacts.2
    exact setAgain cleared checked ▸ run
  have prepareCheck : Steps P host ⟨atBytes cleared, f, expression checkCode⟩
      ⟨atBytes checked, checkedFrame, []⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨0⟩) (v := .i32 0) (f := f) rfl)) ?_
    exact (checkRun.ctxtInstrs (vs := []) (rest := [.plain (.localSet ⟨8⟩)])).tail
      (.variable (.localSet (x := ⟨8⟩) (v := .i32 0) (show 8 < 11 by decide)))
  have writeHigh : Steps P host ⟨atBytes checked, checkedFrame, expression (diagnostic 8 19917)⟩
      ⟨atBytes high, checkedFrame, []⟩ := by
    have run := writeDiagnostic 8 19917 (P := P) (host := host) rfl (mapped checked)
      (by rw [checkedFacts.1, clearedFacts.1]; omega)
    exact setAgain checked high ▸ run
  have writeMiddle : Steps P host ⟨atBytes high, checkedFrame, expression (diagnostic 4 149304)⟩
      ⟨atBytes middle, checkedFrame, []⟩ := by
    have run := writeDiagnostic 4 149304 (P := P) (host := host) rfl (mapped high)
      (by change 126104 ≤ high.size; rw [highFacts.1, checkedFacts.1, clearedFacts.1]; omega)
    exact setAgain high middle ▸ run
  have writeFinal : Steps P host ⟨atBytes middle, checkedFrame, expression (diagnostic 0 12389)⟩
      ⟨atBytes final, checkedFrame, []⟩ := by
    have run := writeDiagnostic 0 12389 (P := P) (host := host) rfl (mapped middle)
      (by change 126100 ≤ middle.size; rw [middleFacts.1, highFacts.1, checkedFacts.1, clearedFacts.1]; omega)
    exact setAgain middle final ▸ run
  have logRun := reactorLogDisabledCall P host (s := atBytes final) (caller := finish)
    21 17113 126096 logSource logSig logSlot logEntry stackSlot stackLow (mapped final) finalFacts.2
  have report : Steps P host ⟨atBytes final, checkedFrame, expression reportCode⟩
      ⟨atBytes final, finish, [.plain (.br ⟨1⟩)]⟩ := by
    refine advance [] (head := [constI32 21, .plain (.localSet ⟨8⟩)])
      (.variable (.localSet (x := ⟨8⟩) (v := .i32 21) (show 8 < 11 by decide))) ?_
    refine advance [.i32 21, .i32 17113] (head := [.plain (.localGet ⟨7⟩)])
      (.variable (.localGet (x := ⟨7⟩) (v := .i32 126096) (f := finish) rfl)) ?_
    exact logRun.ctxtInstrs (vs := []) (rest := [.plain (.br ⟨1⟩)])
  have rejected : Steps P host ⟨atBytes checked, checkedFrame, expression rejection⟩
      ⟨atBytes final, finish, [.plain (.br ⟨1⟩)]⟩ := by
    simp only [rejection, expression, List.map_append]
    have sql : checkedFrame.local? ⟨1⟩ = some (some (.i32 0)) := rfl
    have guard := skipSqlGuard (P := P) (host := host) (s := atBytes checked) sql
    refine (guard.ctxtInstrs (vs := []) (rest := _)).trans ?_
    refine (writeHigh.ctxtInstrs (vs := []) (rest := _)).trans ?_
    refine (writeMiddle.ctxtInstrs (vs := []) (rest := _)).trans ?_
    exact (writeFinal.ctxtInstrs (vs := []) (rest := _)).trans report
  have inner : Steps P host ⟨atBytes checked, checkedFrame, expression [.block .empty rejection]⟩
      ⟨atBytes final, finish, [.plain (.br ⟨0⟩)]⟩ :=
    (enterBlock.steps.trans (rejected.label (n := 0) (cont := []))).tail
      (Step.brLabelSucc (vs := []) (rest := []) (by decide))
  have bypass : Steps P host
      ⟨atBytes checked, checkedFrame, expression [.block .empty (.block .empty rejection :: remainder)]⟩
      ⟨atBytes final, finish, []⟩ :=
    (enterBlock.steps.trans ((inner.ctxtInstrs (vs := []) (rest := expression remainder)).label
      (n := 0) (cont := []))).tail (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)
  have restoreSlot : (atBytes final).global? finish ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 126096⟩) := by
    change (mi.globals[0]?.bind fun a => lowered.globals[a]?.bind fun g => some (a, g)) = _
    rw [stackSlot, Option.bind_some, stackLow]
    rfl
  have restored : (atBytes final).setGlobal stack (.i32 126112) = output := by
    change (output.setGlobal stack (.i32 126096)).setGlobal stack (.i32 126112) = output
    rw [Silmaril.Wasm.Auto.Equiv.setGlobal_setGlobal]
    apply Silmaril.Wasm.Auto.Bridge.setGlobal_self
    change s.globals[stack]?.map (·.value) = some (.i32 126112)
    rw [stackEntry]
    rfl
  have restore : Steps P host ⟨atBytes final, finish, expression epilogue⟩
      ⟨output, finish, [constI32 21]⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨7⟩) (v := .i32 126096) (f := finish) rfl)) ?_
    refine advance [] (head := [constI32 126096, constI32 16, .plain (.intBinOp .i32 .add)])
      (.numeric (.intBinOp (t := .i32) (op := .add) (x := 126096) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 126112, .plain (.globalSet ⟨0⟩)])
      (.variable (.globalSet (v := .i32 126112) restoreSlot)) ?_
    rw [restored]
    exact (Step.variable (.localGet (x := ⟨8⟩) (v := .i32 21) (f := finish) rfl)).steps
  refine ⟨finalOut, finish, ?_⟩
  simp only [suffix, expression, List.map_append]
  exact (prepareCheck.ctxtInstrs (vs := []) (rest := _)).trans
    ((bypass.ctxtInstrs (vs := []) (rest := expression epilogue)).trans restore)

/-- The named prepared export rejects null database and SQL arguments.
The output word and both scratch ranges stay disjoint. The callback word
must read zero in the mapped memory, and the exact final store retains all
five ordered writes with the original stack global restored. -/
theorem reactorPreparedPrepareV2NullRejection (P : Profile) (host : HostSemantics Nat)
    (nByte stmtOut tailOut : BitVec 32) (bound : stmtOut.toNat + 4 ≤ 131072)
    (outCallback : 53000 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 52996)
    (outCheckScratch : 126084 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 126080)
    (outReportScratch : 126108 ≤ stmtOut.toNat ∨ stmtOut.toNat + 4 ≤ 126096) :
    let args : List Val := [.i32 0, .i32 0, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    ∃ runtime frame address helperAddress checkAddress logAddress wrapper helperFn checkFn logFn
        wrapperTy helperTy checkTy logTy stack memory mem,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_prepare_v2") =
        some ⟨"sqlite3_prepare_v2", .func address⟩ ∧
      frame.module.funcs[113]? = some address ∧ frame.module.funcs[105]? = some helperAddress ∧
      frame.module.funcs[130]? = some checkAddress ∧ frame.module.funcs[26]? = some logAddress ∧
      definedFunction? sqlite 113 = some wrapper ∧ definedFunction? sqlite 105 = some helperFn ∧
      definedFunction? sqlite 130 = some checkFn ∧ definedFunction? sqlite 26 = some logFn ∧
      (allocTypes sqlite.types)[checkFn.type.toNat]? = some checkTy ∧
      (allocTypes sqlite.types)[logFn.type.toNat]? = some logTy ∧
      runtime.funcs[address]? = some ⟨wrapperTy, frame.module, .wasm wrapper⟩ ∧
      runtime.funcs[helperAddress]? = some ⟨helperTy, frame.module, .wasm helperFn⟩ ∧
      runtime.funcs[checkAddress]? = some ⟨checkTy, frame.module, .wasm checkFn⟩ ∧
      runtime.funcs[logAddress]? = some ⟨logTy, frame.module, .wasm logFn⟩ ∧
      runtime.global? frame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) ∧
      runtime.mem? frame ⟨0⟩ = some (memory, mem) ∧
      stmtOut.toNat + 4 ≤ mem.bytes.size ∧ 126108 ≤ mem.bytes.size ∧
      InvokeOk runtime address args ∧
      (Memory.load mem.bytes 52996 4 = some 0 →
        Memory.load (prepareV2NullRejectionBytes mem.bytes stmtOut.toNat) stmtOut.toNat 4 = some 0 ∧
        Steps P host (invoke runtime address args)
          ⟨runtime.setMem memory
            { mem with bytes := prepareV2NullRejectionBytes mem.bytes stmtOut.toNat },
            {}, [constI32 21]⟩) := by
  obtain ⟨runtime, frame, address, helperAddress, wrapper, helperFn, stack, memory, mem,
      prepared, exported, slot, helperSlot, wrapperSource, helperSource, stackMapped, memMapped, typed, entered⟩ :=
    reactorPreparedPrepareV2ClearsOutput P host 0 0 nByte stmtOut tailOut bound
  obtain ⟨before, _, sameRuntime, sameFrame, sameMem, samePrepared, alloc, sameFunctions, _, _, sameMapped,
      size, _, _, _⟩ := reactorDirectPreparationWithGlobals
  obtain ⟨runtimeEq, frameAndStart⟩ := Prod.mk.inj (Option.some.inj (samePrepared.symm.trans prepared))
  obtain ⟨frameEq, _⟩ := Prod.mk.inj frameAndStart
  subst sameRuntime sameFrame
  obtain ⟨_, memEq⟩ := Prod.mk.inj (Option.some.inj (sameMapped.symm.trans memMapped))
  subst sameMem
  have known : definedFunction? sqlite 105 = some helper := by kernel_rfl
  have helperEq := Option.some.inj (helperSource.symm.trans known)
  subst helperFn
  have knownWrapper : definedFunction? sqlite 113 = some wrapperCode := by kernel_rfl
  have wrapperEq := Option.some.inj (wrapperSource.symm.trans knownWrapper)
  subst wrapper
  have hWrapper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 90) (fn := wrapperCode) (d := wrapperType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have hHelper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 82) (fn := helper) (d := helperType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have wrapperSlot : frame.module.funcs[113]? = some (before.funcs.length + 90) := by
    simpa only [List.length_range] using hWrapper.1
  have allocatedHelper : frame.module.funcs[105]? = some (before.funcs.length + 82) := by
    simpa only [List.length_range] using hHelper.1
  have wrapperAddrEq := Option.some.inj (slot.symm.trans wrapperSlot)
  have helperAddrEq := Option.some.inj (helperSlot.symm.trans allocatedHelper)
  have wrapperEntry : runtime.funcs[address]? = some ⟨wrapperType, frame.module, .wasm wrapperCode⟩ := by
    rw [wrapperAddrEq, sameFunctions]
    exact hWrapper.2
  have helperEntry : runtime.funcs[helperAddress]? = some ⟨helperType, frame.module, .wasm helper⟩ := by
    rw [helperAddrEq, sameFunctions]
    exact hHelper.2
  have hCheck := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 107) (fn := check) (d := checkType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have hLog := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 3) (fn := logger) (d := loggerType) alloc
    (by kernel_rfl) (by kernel_rfl)
  let checkAddr := before.funcs.length + 107
  let logAddr := before.funcs.length + 3
  have checkSlot : frame.module.funcs[130]? = some checkAddr := by
    simpa only [List.length_range] using hCheck.1
  have logSlot : frame.module.funcs[26]? = some logAddr := by
    simpa only [List.length_range] using hLog.1
  have checkEntry : runtime.funcs[checkAddr]? = some ⟨checkType, frame.module, .wasm check⟩ :=
    sameFunctions.symm ▸ hCheck.2
  have logEntry : runtime.funcs[logAddr]? = some ⟨loggerType, frame.module, .wasm logger⟩ :=
    sameFunctions.symm ▸ hLog.2
  have fits : stmtOut.toNat + 4 ≤ mem.bytes.size := size.symm ▸ bound
  have scratchFits : 126108 ≤ mem.bytes.size := by rw [size]; decide
  refine ⟨runtime, frame, address, helperAddress, checkAddr, logAddr, wrapperCode, helper, check, logger,
    wrapperType, helperType, checkType, loggerType, stack, memory, mem, prepared, exported, slot, helperSlot, checkSlot, logSlot,
    knownWrapper, known, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl,
    wrapperEntry, helperEntry, checkEntry, logEntry,
    stackMapped, memMapped, fits, scratchFits, typed, ?_⟩
  intro zero
  have stackLookups := stackMapped
  change (frame.module.globals[0]?.bind fun a => runtime.globals[a]?.bind fun g => some (a, g)) =
    some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) at stackLookups
  obtain ⟨a, stackSlot, rest⟩ := Option.bind_eq_some_iff.mp stackLookups
  obtain ⟨g, stackEntry, eq⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj eq)
  have memLookups := memMapped
  change (frame.module.mems[0]?.bind fun a => runtime.mems[a]?.bind fun m => some (a, m)) =
    some (memory, mem) at memLookups
  obtain ⟨a, memorySlot, rest⟩ := Option.bind_eq_some_iff.mp memLookups
  obtain ⟨m, memoryEntry, eq⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj eq)
  obtain ⟨outputZero, _, run⟩ := rejectSuffix P host nByte stmtOut tailOut checkSlot checkEntry logSlot logEntry
    stackSlot stackEntry memorySlot memoryEntry fits scratchFits outCallback outCheckScratch outReportScratch zero
  refine ⟨outputZero, ?_⟩
  let args : List Val := [.i32 0, .i32 0, .i32 nByte, .i32 stmtOut, .i32 tailOut]
  let suspended := Frame.forCall frame.module args wrapperCode.locals
  have helperDone := (run.label (n := 1) (cont := [])).tail (Step.labelVals (vs := [.i32 21]))
  have wrapperResumed := (Steps.frame helperDone (f := suspended) (n := 1)).tail
    (Step.frameVals (vs := [.i32 21]) rfl)
  have wrapperDone := (Steps.label wrapperResumed (n := 1) (cont := [])).tail
    (Step.labelVals (vs := [.i32 21]))
  exact entered.trans ((Steps.frame wrapperDone (f := {}) (n := 1)).tail (Step.frameVals (vs := [.i32 21]) rfl))

#print axioms reactorPreparedPrepareV2NullRejection

end SqliteWasm
