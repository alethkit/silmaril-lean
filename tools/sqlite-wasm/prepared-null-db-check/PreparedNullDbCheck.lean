module

public import SqliteWasm.PreparedLogDisabled
import Silmaril.Wasm.Auto.Bridge.Thms
import Silmaril.Wasm.Auto.Equiv.Thms
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private def check : Func := (definedFunction? sqlite 130).get (by kernel_rfl)
private def checkType : DefType := ((allocTypes sqlite.types)[check.type.toNat]?).get (by kernel_rfl)

private def prologue : List Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 16, .intBinOp .i32 .sub, .localTee ⟨1⟩, .globalSet ⟨0⟩]

private def nullGuard : List Instr :=
  [.localGet ⟨0⟩, .brIf ⟨0⟩, .intConst .i32 18995, .localSet ⟨0⟩, .br ⟨1⟩]

private def nonNull : List Instr :=
  match check.body[5]? with
  | some (Instr.block .empty
      (Instr.block .empty (Instr.block .empty (_ :: rest) :: _) :: _)) => rest
  | _ => []

private def diagnostic : List Instr :=
  [.localGet ⟨1⟩, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨2, 0⟩,
    .intConst .i32 21, .intConst .i32 8678, .localGet ⟨1⟩, .call ⟨26⟩]

private def reset : List Instr := [.intConst .i32 0, .localSet ⟨0⟩]

private def epilogue : List Instr :=
  [.localGet ⟨1⟩, .intConst .i32 16, .intBinOp .i32 .add, .globalSet ⟨0⟩, .localGet ⟨0⟩]

private theorem checkBody :
    check.body = prologue ++ [.block .empty
      ([.block .empty (.block .empty (.block .empty nullGuard :: nonNull) :: diagnostic)] ++ reset)] ++
      epilogue := by
  kernel_rfl

private theorem advance {H : Type} {P : Profile} {host : HostSemantics H}
    {s s' : Store H} {f f' : Frame} {head next rest : List Admin} {finish : Config H}
    (operands : List Val) (step : Step P host ⟨s, f, head⟩ ⟨s', f', next⟩)
    (tail : Steps P host ⟨s', f', vals operands ++ next ++ rest⟩ finish) :
    Steps P host ⟨s, f, vals operands ++ head ++ rest⟩ finish :=
  (step.steps.ctxtInstrs (vs := operands) (rest := rest)).trans tail

private theorem enterBlock {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {code : List Instr} :
    Step P host ⟨s, f, expression [.block .empty code]⟩ ⟨s, f, [.label 0 [] (expression code)]⟩ :=
  Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl

private theorem emptyBlock {H : Type} {P : Profile} {host : HostSemantics H}
    {s s' : Store H} {f f' : Frame} {code : List Instr}
    (run : Steps P host ⟨s, f, expression code⟩ ⟨s', f', []⟩) :
    Steps P host ⟨s, f, expression [.block .empty code]⟩ ⟨s', f', []⟩ :=
  (enterBlock.steps.trans (run.label (n := 0) (cont := []))).tail (Step.labelVals (vs := []))

private theorem lookupStack {H : Type} {s : Store H} {f : Frame} {stack : Nat} {sp : BitVec 32}
    (slot : f.module.globals[0]? = some stack)
    (entry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 sp⟩) :
    s.global? f ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 sp⟩) := by
  change (f.module.globals[0]?.bind fun a => s.globals[a]?.bind fun g => some (a, g)) = _
  rw [slot, Option.bind_some, entry]
  rfl

/-- The pinned slot-130 null check reaches its disabled diagnostic path.
The result is i32 zero in the original caller, with precisely the scratch
word written and the original stack global restored. -/
theorem reactorNullDbCheck {H : Type} (P : Profile) (host : HostSemantics H)
    {s : Store H} {caller : Frame} {address logAddress stack memory : Nat} {sp : BitVec 32}
    {fn logFn : Func} {type logType : DefType} {mem : MemInst}
    (source : definedFunction? sqlite 130 = some fn)
    (closedType : (allocTypes sqlite.types)[fn.type.toNat]? = some type)
    (slot : caller.module.funcs[130]? = some address)
    (entry : s.funcs[address]? = some ⟨type, caller.module, .wasm fn⟩)
    (logSource : definedFunction? sqlite 26 = some logFn)
    (logClosedType : (allocTypes sqlite.types)[logFn.type.toNat]? = some logType)
    (logSlot : caller.module.funcs[26]? = some logAddress)
    (logEntry : s.funcs[logAddress]? = some ⟨logType, caller.module, .wasm logFn⟩)
    (stackSlot : caller.module.globals[0]? = some stack)
    (stackEntry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 sp⟩)
    (memorySlot : caller.module.mems[0]? = some memory)
    (memoryEntry : s.mems[memory]? = some mem)
    (fits : (sp - 16#32).toNat + 4 ≤ mem.bytes.size)
    (disjoint : 52996 + 4 ≤ (sp - 16#32).toNat ∨ (sp - 16#32).toNat + 4 ≤ 52996)
    (callbackZero : Memory.load mem.bytes 52996 4 = some 0) :
    let scratch := (sp - 16#32).toNat
    let bytes := Memory.writeSlice mem.bytes scratch (Memory.encodeLE 4 18995)
    Steps P host ⟨s, caller, [constI32 0, .plain (.call ⟨130⟩)]⟩
      ⟨s.setMem memory { mem with bytes }, caller, [constI32 0]⟩ := by
  have known : definedFunction? sqlite 130 = some check := by kernel_rfl
  have sameFn := Option.some.inj (source.symm.trans known)
  subst fn
  have knownType : (allocTypes sqlite.types)[check.type.toNat]? = some checkType := by kernel_rfl
  have sameType := Option.some.inj (closedType.symm.trans knownType)
  subst type
  let start := Frame.forCall caller.module [.i32 0] check.locals
  let scratch := sp - 16#32
  let withStack := start.setLocal ⟨1⟩ (.i32 scratch)
  let withDiagnostic := withStack.setLocal ⟨0⟩ (.i32 18995)
  let finished := withDiagnostic.setLocal ⟨0⟩ (.i32 0)
  let lowered := s.setGlobal stack (.i32 scratch)
  let bytes := Memory.writeSlice mem.bytes scratch.toNat (Memory.encodeLE 4 18995)
  let updatedMem := { mem with bytes }
  let written := lowered.setMem memory updatedMem
  let output := s.setMem memory updatedMem
  have preStack : s.global? start ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 sp⟩) :=
    lookupStack stackSlot stackEntry
  have stackForSet : s.global? withStack ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 sp⟩) :=
    lookupStack stackSlot stackEntry
  have lower : Steps P host ⟨s, start, expression prologue⟩ ⟨lowered, withStack, []⟩ := by
    unfold prologue expression
    refine advance [] (.variable (.globalGet preStack)) ?_
    refine advance [] (head := [constI32 sp, constI32 16, .plain (.intBinOp .i32 .sub)])
      (.numeric (.intBinOp (t := .i32) (op := .sub) (x := sp) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 scratch, .plain (.localTee ⟨1⟩)])
      (.variable (.localTee (x := ⟨1⟩) (v := .i32 scratch))) ?_
    refine advance [.i32 scratch] (head := [constI32 scratch, .plain (.localSet ⟨1⟩)])
      (.variable (.localSet (f := start) (x := ⟨1⟩) (v := .i32 scratch)
        (show 1 < 2 by decide))) ?_
    exact (Step.variable (.globalSet (v := .i32 scratch) stackForSet)).steps
  have guard : Steps P host ⟨lowered, withStack, expression nullGuard⟩
      ⟨lowered, withDiagnostic, [.plain (.br ⟨1⟩)]⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨0⟩) (v := .i32 0) (f := withStack) rfl)) ?_
    refine advance [] (head := [constI32 0, .plain (.brIf ⟨0⟩)]) Step.brIfFalse ?_
    refine advance [] (head := [constI32 18995, .plain (.localSet ⟨0⟩)])
      (.variable (.localSet (f := withStack) (x := ⟨0⟩) (v := .i32 18995)
        (show 0 < 2 by decide))) ?_
    exact .refl
  have inner : Steps P host ⟨lowered, withStack, expression [.block .empty nullGuard]⟩
      ⟨lowered, withDiagnostic, [.plain (.br ⟨0⟩)]⟩ :=
    (enterBlock.steps.trans (guard.label (n := 0) (cont := []))).tail
      (Step.brLabelSucc (vs := []) (rest := []) (by decide))
  let selection := .block .empty nullGuard :: nonNull
  have selected : Steps P host ⟨lowered, withStack, expression [.block .empty selection]⟩
      ⟨lowered, withDiagnostic, []⟩ :=
    (enterBlock.steps.trans ((inner.ctxtInstrs (vs := []) (rest := expression nonNull)).label
      (n := 0) (cont := []))).tail (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)
  have mapped : lowered.mem? withDiagnostic ⟨0⟩ = some (memory, mem) := by
    change (caller.module.mems[0]?.bind fun a => s.mems[a]?.bind fun m => some (a, m)) = _
    rw [memorySlot, Option.bind_some, memoryEntry]
    rfl
  have write : Memory.writeBytes mem.bytes scratch.toNat (Memory.encodeLE 4 18995) = some bytes := by
    rw [Memory.writeBytes, Memory.encodeLE_size, ite_eq_left fits]
  have writeStep : Step P host ⟨lowered, withDiagnostic, [constI32 scratch, constI32 18995,
      .plain (.intStore .i32 none ⟨0⟩ ⟨2, 0⟩)]⟩ ⟨written, withDiagnostic, []⟩ := by
    apply Step.memory
    refine MemoryStep.storeIntVal (t := .i32) (arg := ⟨2, 0⟩)
      (a := .i32) (i := scratch) (c := 18995#32) mapped ?_
    change Memory.writeBytes mem.bytes (scratch.toNat + 0) (Memory.encodeLE 4 18995) = some bytes
    simpa only [Nat.add_zero] using write
  have mappedWritten : written.mem? withDiagnostic ⟨0⟩ = some (memory, updatedMem) := by
    have index := (List.getElem?_eq_some_iff.mp memoryEntry).1
    change (caller.module.mems[0]?.bind fun a =>
      (s.mems.set memory updatedMem)[a]?.bind fun m => some (a, m)) = _
    rw [memorySlot, Option.bind_some, List.getElem?_set_self index]
    rfl
  have zeroWritten : Memory.load bytes 52996 4 = some 0 := by
    have separate : 52996 + 4 ≤ scratch.toNat ∨ scratch.toNat + (Memory.encodeLE 4 18995).size ≤ 52996 := by
      simpa only [Memory.encodeLE_size] using disjoint
    unfold Memory.load at callbackZero ⊢
    rw [Memory.readBytes_writeBytes_disjoint _ _ _ _ _ _ write separate]
    exact callbackZero
  have loweredEntry : written.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 scratch⟩ := by
    simp [written, lowered, Store.setMem, Store.setGlobal, stackEntry]
  have logRun := reactorLogDisabledCall P host (s := written) (caller := withDiagnostic)
    21 8678 scratch logSource logClosedType logSlot logEntry stackSlot loweredEntry mappedWritten zeroWritten
  have report : Steps P host ⟨lowered, withDiagnostic, expression diagnostic⟩
      ⟨written, withDiagnostic, []⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨1⟩) (v := .i32 scratch) (f := withDiagnostic) rfl)) ?_
    refine advance [.i32 scratch] (head := [.plain (.localGet ⟨0⟩)])
      (.variable (.localGet (x := ⟨0⟩) (v := .i32 18995) (f := withDiagnostic) rfl)) ?_
    refine advance [] (head := [constI32 scratch, constI32 18995, .plain (.intStore .i32 none ⟨0⟩ ⟨2, 0⟩)])
      writeStep ?_
    refine advance [.i32 21, .i32 8678] (head := [.plain (.localGet ⟨1⟩)])
      (.variable (.localGet (x := ⟨1⟩) (v := .i32 scratch) (f := withDiagnostic) rfl)) ?_
    exact logRun
  have diagnosticBlock : Steps P host
      ⟨lowered, withStack, expression [.block .empty (.block .empty selection :: diagnostic)]⟩
      ⟨written, withDiagnostic, []⟩ :=
    emptyBlock ((selected.ctxtInstrs (vs := []) (rest := expression diagnostic)).trans report)
  have result : Steps P host ⟨written, withDiagnostic, expression reset⟩ ⟨written, finished, []⟩ :=
    (Step.variable (.localSet (f := withDiagnostic) (x := ⟨0⟩) (v := .i32 0)
      (show 0 < 2 by decide))).steps
  have selectedNull : Steps P host ⟨lowered, withStack,
      expression [.block .empty ([.block .empty (.block .empty selection :: diagnostic)] ++ reset)]⟩
      ⟨written, finished, []⟩ :=
    emptyBlock ((diagnosticBlock.ctxtInstrs (vs := []) (rest := expression reset)).trans result)
  have restored : written.setGlobal stack (.i32 sp) = output := by
    change ((output.setGlobal stack (.i32 scratch)).setGlobal stack (.i32 sp)) = output
    rw [Silmaril.Wasm.Auto.Equiv.setGlobal_setGlobal]
    apply Silmaril.Wasm.Auto.Bridge.setGlobal_self
    change s.globals[stack]?.map (·.value) = some (.i32 sp)
    rw [stackEntry]
    rfl
  have finalStack : written.global? finished ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 scratch⟩) := lookupStack stackSlot loweredEntry
  have finish : Steps P host ⟨written, finished, expression epilogue⟩ ⟨output, finished, [constI32 0]⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨1⟩) (v := .i32 scratch) (f := finished) rfl)) ?_
    refine advance [] (head := [constI32 scratch, constI32 16, .plain (.intBinOp .i32 .add)])
      (.numeric (.intBinOp (t := .i32) (op := .add) (x := scratch) (y := 16)
        (congrArg Except.ok (BitVec.sub_add_cancel sp 16)))) ?_
    refine advance [] (head := [constI32 sp, .plain (.globalSet ⟨0⟩)])
      (.variable (.globalSet (v := .i32 sp) finalStack)) ?_
    rw [restored]
    exact (Step.variable (.localGet (x := ⟨0⟩) (v := .i32 0) (f := finished) rfl)).steps
  have body : Steps P host ⟨s, start, expression check.body⟩ ⟨output, finished, [constI32 0]⟩ := by
    simp only [checkBody, expression, List.map_append]
    exact (lower.ctxtInstrs (vs := []) (rest := _)).trans
      ((selectedNull.ctxtInstrs (vs := []) (rest := expression epilogue)).trans finish)
  have signature : Expand checkType (.func (.cons Ty.i32 .nil) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  have call := Step.call (P := P) (host := host) (f := caller) (x := ⟨130⟩) slot entry
  have enter := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType checkType) (vs := [.i32 0]) trivial entry signature rfl rfl
  have innerFrame : Steps P host ⟨s, start, [.label 1 [] (expression check.body)]⟩
      ⟨output, finished, [constI32 0]⟩ :=
    (body.label (n := 1) (cont := [])).tail (Step.labelVals (vs := [.i32 0]))
  exact ((call.steps.ctxtInstrs (vs := [.i32 0]) (rest := [])).tail enter).trans
    ((innerFrame.frame (f := caller) (n := 1)).tail (Step.frameVals (vs := [.i32 0]) rfl))

#print axioms reactorNullDbCheck

end SqliteWasm
