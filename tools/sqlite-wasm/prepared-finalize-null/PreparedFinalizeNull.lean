module

public import SqliteWasm.DirectPreparation
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Auto.Bridge.Thms
import Silmaril.Wasm.Auto.Equiv.Thms
import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CGlobalType DefType Expand Ty liftVal)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private def finalize : Func := (definedFunction? sqlite 111).get (by kernel_rfl)
private def finalizeType : DefType := ((allocTypes sqlite.types)[finalize.type.toNat]?).get (by kernel_rfl)

private def prologue : List Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 16, .intBinOp .i32 .sub, .localTee ⟨1⟩, .globalSet ⟨0⟩]

private def nullGuard : List Instr :=
  [.localGet ⟨0⟩, .brIf ⟨0⟩, .intConst .i32 0, .localSet ⟨0⟩, .br ⟨1⟩]

private def statementCode : List Instr :=
  match (finalize.body : List Instr)[5]? with
  | some (Instr.block .empty body) => body.tail
  | _ => []

private def epilogue : List Instr :=
  [.localGet ⟨1⟩, .intConst .i32 16, .intBinOp .i32 .add, .globalSet ⟨0⟩, .localGet ⟨0⟩]

private theorem finalizeBody :
    finalize.body = prologue ++ [.block .empty (.block .empty nullGuard :: statementCode)] ++ epilogue := by
  kernel_rfl

private theorem advance {P : Profile} {host : HostSemantics Nat}
    {s s' : Store Nat} {f f' : Frame} {head next rest : List Admin} {finish : Config Nat}
    (values : List Val) (step : Step P host ⟨s, f, head⟩ ⟨s', f', next⟩)
    (tail : Steps P host ⟨s', f', vals values ++ next ++ rest⟩ finish) :
    Steps P host ⟨s, f, vals values ++ head ++ rest⟩ finish :=
  (step.steps.ctxtInstrs (vs := values) (rest := rest)).trans tail

private theorem bodyReturnsZero {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {mi : ModuleInst} {stack : Nat}
    (slot : mi.globals[0]? = some stack)
    (entry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126112⟩) :
    ∃ finish,
      Steps P host ⟨s, Frame.forCall mi [.i32 0] finalize.locals, expression finalize.body⟩
        ⟨s, finish, [constI32 0]⟩ := by
  let start := Frame.forCall mi [.i32 0] finalize.locals
  let withStack := start.setLocal ⟨1⟩ (.i32 126096)
  let resultFrame := withStack.setLocal ⟨0⟩ (.i32 0)
  let lowered := s.setGlobal stack (.i32 126096)
  have before : s.global? start ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) := by
    change (mi.globals[0]?.bind fun a => s.globals[a]?.bind fun g => some (a, g)) = _
    rw [slot, Option.bind_some, entry]
    rfl
  have beforeSet : s.global? withStack ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) := before
  have loweredEntry : lowered.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126096⟩ := by
    simp [lowered, Store.setGlobal, entry]
  have after : lowered.global? resultFrame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126096⟩) := by
    change (mi.globals[0]?.bind fun a => lowered.globals[a]?.bind fun g => some (a, g)) = _
    rw [slot, Option.bind_some, loweredEntry]
    rfl
  have restored : lowered.setGlobal stack (.i32 126112) = s := by
    change (s.setGlobal stack (.i32 126096)).setGlobal stack (.i32 126112) = s
    rw [Silmaril.Wasm.Auto.Equiv.setGlobal_setGlobal]
    apply Silmaril.Wasm.Auto.Bridge.setGlobal_self
    rw [entry]
    rfl
  have lower : Steps P host ⟨s, start, expression prologue⟩ ⟨lowered, withStack, []⟩ := by
    refine advance [] (.variable (.globalGet before)) ?_
    refine advance [] (head := [constI32 126112, constI32 16, .plain (.intBinOp .i32 .sub)])
      (.numeric (.intBinOp (t := .i32) (op := .sub) (x := 126112) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 126096, .plain (.localTee ⟨1⟩)])
      (.variable (.localTee (x := ⟨1⟩) (v := .i32 126096))) ?_
    refine advance [.i32 126096] (head := [constI32 126096, .plain (.localSet ⟨1⟩)])
      (.variable (.localSet (f := start) (x := ⟨1⟩) (v := .i32 126096)
        (show 1 < 4 by decide))) ?_
    exact (Step.variable (.globalSet (v := .i32 126096) beforeSet)).steps
  have guard : Steps P host ⟨lowered, withStack, expression nullGuard⟩
      ⟨lowered, resultFrame, [.plain (.br ⟨1⟩)]⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨0⟩) (v := .i32 0) (f := withStack) rfl)) ?_
    refine advance [] (head := [constI32 0, .plain (.brIf ⟨0⟩)]) Step.brIfFalse ?_
    refine advance [] (head := [constI32 0, .plain (.localSet ⟨0⟩)])
      (.variable (.localSet (f := withStack) (x := ⟨0⟩) (v := .i32 0)
        (show 0 < 4 by decide))) ?_
    exact .refl
  have innerEnter : Step P host ⟨lowered, withStack, expression [.block .empty nullGuard]⟩
      ⟨lowered, withStack, [.label 0 [] (expression nullGuard)]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have inner : Steps P host ⟨lowered, withStack, expression [.block .empty nullGuard]⟩
      ⟨lowered, resultFrame, [.plain (.br ⟨0⟩)]⟩ :=
    (innerEnter.steps.trans (guard.label (n := 0) (cont := []))).tail
      (Step.brLabelSucc (vs := []) (rest := []) (by decide))
  let outerBody := .block .empty nullGuard :: statementCode
  have outerEnter : Step P host ⟨lowered, withStack, expression [.block .empty outerBody]⟩
      ⟨lowered, withStack, [.label 0 [] (expression outerBody)]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have bypass : Steps P host ⟨lowered, withStack, expression [.block .empty outerBody]⟩
      ⟨lowered, resultFrame, []⟩ :=
    (outerEnter.steps.trans ((inner.ctxtInstrs (vs := []) (rest := expression statementCode)).label
      (n := 0) (cont := []))).tail (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)
  have finish : Steps P host ⟨lowered, resultFrame, expression epilogue⟩ ⟨s, resultFrame, [constI32 0]⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨1⟩) (v := .i32 126096) (f := resultFrame) rfl)) ?_
    refine advance [] (head := [constI32 126096, constI32 16, .plain (.intBinOp .i32 .add)])
      (.numeric (.intBinOp (t := .i32) (op := .add) (x := 126096) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 126112, .plain (.globalSet ⟨0⟩)])
      (.variable (.globalSet (v := .i32 126112) after)) ?_
    rw [restored]
    exact (Step.variable (.localGet (x := ⟨0⟩) (v := .i32 0) (f := resultFrame) rfl)).steps
  refine ⟨resultFrame, ?_⟩
  rw [finalizeBody]
  change Steps P host ⟨s, start, expression prologue ++
    (expression [.block .empty outerBody] ++ expression epilogue)⟩ _
  exact (lower.ctxtInstrs (vs := []) (rest := _)).trans
    ((bypass.ctxtInstrs (vs := []) (rest := expression epilogue)).trans finish)

private theorem finalizeReturnsZero {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {mi : ModuleInst} {address stack : Nat}
    (entry : s.funcs[address]? = some ⟨finalizeType, mi, .wasm finalize⟩)
    (stackSlot : mi.globals[0]? = some stack)
    (stackEntry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126112⟩) :
    InvokeOk s address [.i32 0] ∧
    Steps P host (invoke s address [.i32 0]) ⟨s, {}, [constI32 0]⟩ := by
  have signature : Expand finalizeType (.func (.cons Ty.i32 .nil) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  let frame := Frame.forCall mi [.i32 0] finalize.locals
  have enter : Step P host (invoke s address [.i32 0])
      ⟨s, {}, [.frame 1 frame [.label 1 [] (expression finalize.body)]]⟩ := by
    unfold invoke
    rw [entry]
    exact Step.callRefFunc (c := .callRefType finalizeType) (vs := [.i32 0])
      trivial entry signature rfl rfl
  obtain ⟨returnedFrame, run⟩ := bodyReturnsZero (P := P) (host := host) stackSlot stackEntry
  have label : Steps P host ⟨s, frame, [.label 1 [] (expression finalize.body)]⟩
      ⟨s, returnedFrame, [constI32 0]⟩ :=
    (run.label (n := 1) (cont := [])).tail (Step.labelVals (vs := [.i32 0]))
  have result := (label.frame (f := ({} : Frame)) (n := 1)).tail (Step.frameVals (vs := [.i32 0]) rfl)
  exact ⟨⟨_, .cons Ty.i32 .nil, .cons Ty.i32 .nil, entry, signature, .cons (.num _) .nil⟩,
    enter.steps.trans result⟩

private theorem allocatedExports {s allocated : Store Nat} {m : Module} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref} {elements : List (List Ref)}
    (alloc : allocModule? s m imports globals tables elements = some (allocated, mi)) :
    m.exports.mapM (allocExport? mi) = some mi.exports := by
  obtain ⟨_, _, _, _, _, built, view, _⟩ := allocModule?_inv alloc
  rw [view]
  convert built using 2
  funext e
  unfold allocExport?
  cases e.index <;> rfl

private theorem findAllocated {mi : ModuleInst} {exports : List Export} {instances : List ExportInst}
    {source : Export} {target : ExportInst} {name : String}
    (built : exports.mapM (allocExport? mi) = some instances)
    (found : exports.find? (·.name == name) = some source)
    (resolved : allocExport? mi source = some target) :
    instances.find? (·.name == name) = some target := by
  induction exports generalizing instances with
  | nil => simp at found
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at built
    obtain ⟨x, head, rest⟩ := Option.bind_eq_some_iff.mp built
    obtain ⟨xs, tail, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl : x :: xs = instances := Option.some.inj rest
    have sameName := (allocExport?_spec head).1
    by_cases named : (e.name == name) = true
    · have sameSource : e = source := by simpa [List.find?_cons, named] using found
      have sameTarget : x = target := Option.some.inj (head.symm.trans (sameSource ▸ resolved))
      rw [List.find?_cons, sameName, named, sameTarget]
    · have later : es.find? (·.name == name) = some source := by
        simpa [List.find?_cons, named] using found
      simpa [List.find?_cons, sameName, named] using ih tail later

private def stackGlobal : Global := (sqlite.globals[0]?).get (by kernel_rfl)

/-- The actual named finalize export returns SQLITE_OK for the null handle in
the directly prepared reactor, with the entire prepared store and empty invoke frame. -/
theorem reactorPreparedFinalizeNull (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_finalize") =
        some ⟨"sqlite3_finalize", .func address⟩ ∧
      frame.module.funcs[111]? = some address ∧
      InvokeOk runtime address [.i32 0] ∧
      Steps P host (invoke runtime address [.i32 0]) ⟨runtime, {}, [constI32 0]⟩ := by
  obtain ⟨before, allocated, runtime, frame, _, prepared, alloc, sameFunctions, _, _, _, _, _, _,
    sameGlobals⟩ := reactorDirectPreparationWithGlobals
  have boundFunction := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 88) (fn := finalize) (d := finalizeType) alloc
    (by kernel_rfl) (by kernel_rfl)
  let address := before.funcs.length + 88
  have slot : frame.module.funcs[111]? = some address := by
    simpa only [List.length_range] using boundFunction.1
  have entry : runtime.funcs[address]? = some ⟨finalizeType, frame.module, .wasm finalize⟩ :=
    sameFunctions.symm ▸ boundFunction.2
  have stack := Link.GC.Preparation.allocModule_global
    (as := List.range 23) (n := 0) (g := stackGlobal) (v := .i32 126112) alloc
    (by kernel_rfl) rfl
  have stackSlot : frame.module.globals[0]? = some before.globals.length := by
    simpa only [Nat.add_zero] using stack.1
  have stackType : (⟨stackGlobal.type.mutability,
      (liftVal stackGlobal.type.value).substAll ((allocTypes sqlite.types).map .dt)⟩ : CGlobalType) =
      ⟨.var, .i32⟩ := by kernel_rfl
  have stackEntry : runtime.globals[before.globals.length]? = some ⟨⟨.var, .i32⟩, .i32 126112⟩ := by
    rw [sameGlobals]
    simpa only [Nat.add_zero, stackType] using stack.2
  have source : sqlite.exports.find? (·.name == "sqlite3_finalize") =
      some ⟨"sqlite3_finalize", .func ⟨111⟩⟩ := by kernel_rfl
  have resolved : allocExport? frame.module ⟨"sqlite3_finalize", .func ⟨111⟩⟩ =
      some ⟨"sqlite3_finalize", .func address⟩ := by
    change (frame.module.funcs[111]?.map ExternAddr.func).map _ = _
    rw [slot]
    rfl
  have exported := findAllocated (allocatedExports alloc) source resolved
  exact ⟨runtime, frame, address, prepared, exported, slot,
    finalizeReturnsZero entry stackSlot stackEntry⟩

#print axioms reactorPreparedFinalizeNull

end SqliteWasm
