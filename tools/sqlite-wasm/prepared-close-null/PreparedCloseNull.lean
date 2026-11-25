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

private def close : Func := (definedFunction? sqlite 295).get (by kernel_rfl)
private def closeImpl : Func := (definedFunction? sqlite 296).get (by kernel_rfl)
private def closeType : DefType := ((allocTypes sqlite.types)[close.type.toNat]?).get (by kernel_rfl)
private def closeImplType : DefType := ((allocTypes sqlite.types)[closeImpl.type.toNat]?).get (by kernel_rfl)

private def prologue : List Instr :=
  [.globalGet ⟨0⟩, .intConst .i32 16, .intBinOp .i32 .sub, .localTee ⟨2⟩,
    .globalSet ⟨0⟩, .intConst .i32 0, .localSet ⟨3⟩]

private def nullGuard : List Instr :=
  [.localGet ⟨0⟩, .intTestOp .i32 .eqz, .brIf ⟨0⟩]

private def connectionCode : List Instr :=
  match (closeImpl.body : List Instr)[7]? with
  | some (Instr.block .empty body) => body.drop 3
  | _ => []

private def epilogue : List Instr :=
  [.localGet ⟨2⟩, .intConst .i32 16, .intBinOp .i32 .add, .globalSet ⟨0⟩, .localGet ⟨3⟩]

private theorem closeBody : close.body = [.localGet ⟨0⟩, .intConst .i32 0, .call ⟨296⟩] := by
  kernel_rfl

private theorem implBody :
    closeImpl.body = prologue ++ [.block .empty (nullGuard ++ connectionCode)] ++ epilogue := by
  kernel_rfl

private theorem advance {P : Profile} {host : HostSemantics Nat}
    {s s' : Store Nat} {f f' : Frame} {head next rest : List Admin} {finish : Config Nat}
    (values : List Val) (step : Step P host ⟨s, f, head⟩ ⟨s', f', next⟩)
    (tail : Steps P host ⟨s', f', vals values ++ next ++ rest⟩ finish) :
    Steps P host ⟨s, f, vals values ++ head ++ rest⟩ finish :=
  (step.steps.ctxtInstrs (vs := values) (rest := rest)).trans tail

private theorem implReturnsZero {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {mi : ModuleInst} {stack : Nat}
    (slot : mi.globals[0]? = some stack)
    (entry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126112⟩) :
    ∃ finish,
      Steps P host ⟨s, Frame.forCall mi [.i32 0, .i32 0] closeImpl.locals, expression closeImpl.body⟩
        ⟨s, finish, [constI32 0]⟩ := by
  let start := Frame.forCall mi [.i32 0, .i32 0] closeImpl.locals
  let withStack := start.setLocal ⟨2⟩ (.i32 126096)
  let bodyFrame := withStack.setLocal ⟨3⟩ (.i32 0)
  let lowered := s.setGlobal stack (.i32 126096)
  have before : s.global? start ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) := by
    change (mi.globals[0]?.bind fun a => s.globals[a]?.bind fun g => some (a, g)) = _
    rw [slot, Option.bind_some, entry]
    rfl
  have beforeSet : s.global? withStack ⟨0⟩ =
      some (stack, ⟨⟨.var, .i32⟩, .i32 126112⟩) := before
  have loweredEntry : lowered.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126096⟩ := by
    simp [lowered, Store.setGlobal, entry]
  have after : lowered.global? bodyFrame ⟨0⟩ = some (stack, ⟨⟨.var, .i32⟩, .i32 126096⟩) := by
    change (mi.globals[0]?.bind fun a => lowered.globals[a]?.bind fun g => some (a, g)) = _
    rw [slot, Option.bind_some, loweredEntry]
    rfl
  have restored : lowered.setGlobal stack (.i32 126112) = s := by
    change (s.setGlobal stack (.i32 126096)).setGlobal stack (.i32 126112) = s
    rw [Silmaril.Wasm.Auto.Equiv.setGlobal_setGlobal]
    apply Silmaril.Wasm.Auto.Bridge.setGlobal_self
    rw [entry]
    rfl
  have lower : Steps P host ⟨s, start, expression prologue⟩ ⟨lowered, bodyFrame, []⟩ := by
    refine advance [] (.variable (.globalGet before)) ?_
    refine advance [] (head := [constI32 126112, constI32 16, .plain (.intBinOp .i32 .sub)])
      (.numeric (.intBinOp (t := .i32) (op := .sub) (x := 126112) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 126096, .plain (.localTee ⟨2⟩)])
      (.variable (.localTee (x := ⟨2⟩) (v := .i32 126096))) ?_
    refine advance [.i32 126096] (head := [constI32 126096, .plain (.localSet ⟨2⟩)])
      (.variable (.localSet (f := start) (x := ⟨2⟩) (v := .i32 126096)
        (show 2 < 8 by decide))) ?_
    refine advance [] (head := [constI32 126096, .plain (.globalSet ⟨0⟩)])
      (.variable (.globalSet (v := .i32 126096) beforeSet)) ?_
    exact (Step.variable (.localSet (f := withStack) (x := ⟨3⟩) (v := .i32 0)
      (show 3 < 8 by decide))).steps
  have guard : Steps P host ⟨lowered, bodyFrame, expression (nullGuard ++ connectionCode)⟩
      ⟨lowered, bodyFrame, [.plain (.br ⟨0⟩)] ++ expression connectionCode⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨0⟩) (v := .i32 0) (f := bodyFrame) rfl)) ?_
    refine advance [] (head := [constI32 0, .plain (.intTestOp .i32 .eqz)])
      (.numeric (.intTestOp (t := .i32) (op := .eqz) (x := 0))) ?_
    exact (Step.brIfTrue (s := lowered) (f := bodyFrame) (c := 1) (l := ⟨0⟩)
      (by decide)).steps.ctxtInstrs (vs := []) (rest := expression connectionCode)
  have bypass : Steps P host ⟨lowered, bodyFrame, expression [.block .empty (nullGuard ++ connectionCode)]⟩
      ⟨lowered, bodyFrame, []⟩ := by
    have enter : Step P host ⟨lowered, bodyFrame, expression [.block .empty (nullGuard ++ connectionCode)]⟩
        ⟨lowered, bodyFrame, [.label 0 [] (expression (nullGuard ++ connectionCode))]⟩ :=
      Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
    exact (enter.steps.trans (guard.label (n := 0) (cont := []))).tail
      (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)
  have finish : Steps P host ⟨lowered, bodyFrame, expression epilogue⟩ ⟨s, bodyFrame, [constI32 0]⟩ := by
    refine advance [] (.variable (.localGet (x := ⟨2⟩) (v := .i32 126096) (f := bodyFrame) rfl)) ?_
    refine advance [] (head := [constI32 126096, constI32 16, .plain (.intBinOp .i32 .add)])
      (.numeric (.intBinOp (t := .i32) (op := .add) (x := 126096) (y := 16) rfl)) ?_
    refine advance [] (head := [constI32 126112, .plain (.globalSet ⟨0⟩)])
      (.variable (.globalSet (v := .i32 126112) after)) ?_
    rw [restored]
    exact (Step.variable (.localGet (x := ⟨3⟩) (v := .i32 0) (f := bodyFrame) rfl)).steps
  refine ⟨bodyFrame, ?_⟩
  rw [implBody]
  change Steps P host ⟨s, start, expression prologue ++
    (expression [.block .empty (nullGuard ++ connectionCode)] ++ expression epilogue)⟩ _
  exact (lower.ctxtInstrs (vs := []) (rest := _)).trans
    ((bypass.ctxtInstrs (vs := []) (rest := expression epilogue)).trans finish)

private theorem returnInFrame {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {caller start finish : Frame} {body : List Admin}
    (run : Steps P host ⟨s, start, body⟩ ⟨s, finish, [constI32 0]⟩) :
    Steps P host ⟨s, caller, [.frame 1 start [.label 1 [] body]]⟩ ⟨s, caller, [constI32 0]⟩ := by
  have label : Steps P host ⟨s, start, [.label 1 [] body]⟩ ⟨s, finish, [constI32 0]⟩ :=
    (run.label (n := 1) (cont := [])).tail (Step.labelVals (vs := [.i32 0]))
  exact (label.frame (f := caller) (n := 1)).tail (Step.frameVals (vs := [.i32 0]) rfl)

private theorem closeReturnsZero {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {mi : ModuleInst} {address helperAddress stack : Nat}
    (entry : s.funcs[address]? = some ⟨closeType, mi, .wasm close⟩)
    (helperSlot : mi.funcs[296]? = some helperAddress)
    (helperEntry : s.funcs[helperAddress]? = some ⟨closeImplType, mi, .wasm closeImpl⟩)
    (stackSlot : mi.globals[0]? = some stack)
    (stackEntry : s.globals[stack]? = some ⟨⟨.var, .i32⟩, .i32 126112⟩) :
    InvokeOk s address [.i32 0] ∧
    Steps P host (invoke s address [.i32 0]) ⟨s, {}, [constI32 0]⟩ := by
  have signature : Expand closeType (.func (.cons Ty.i32 .nil) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  have helperSignature : Expand closeImplType
      (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  let wrapper := Frame.forCall mi [.i32 0] close.locals
  have enter : Step P host (invoke s address [.i32 0])
      ⟨s, {}, [.frame 1 wrapper [.label 1 [] (expression close.body)]]⟩ := by
    unfold invoke
    rw [entry]
    exact Step.callRefFunc (c := .callRefType closeType) (vs := [.i32 0])
      trivial entry signature rfl rfl
  obtain ⟨_, inner⟩ := implReturnsZero (P := P) (host := host) stackSlot stackEntry
  have wrapped : Steps P host ⟨s, wrapper, expression close.body⟩ ⟨s, wrapper, [constI32 0]⟩ := by
    rw [closeBody]
    refine advance [] (.variable (.localGet (f := wrapper) (x := ⟨0⟩) (v := .i32 0) rfl)) ?_
    refine advance [.i32 0, .i32 0] (Step.call (x := ⟨296⟩) helperSlot helperEntry) ?_
    exact (Step.callRefFunc (c := .callRefType closeImplType) (vs := [.i32 0, .i32 0])
      trivial helperEntry helperSignature rfl rfl).steps.trans (returnInFrame inner)
  refine ⟨⟨_, .cons Ty.i32 .nil, .cons Ty.i32 .nil, entry, signature, .cons ?_ .nil⟩, ?_⟩
  · exact .num _
  · exact enter.steps.trans (returnInFrame wrapped)

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

/-- Calling the pinned prepared reactor's named close export with a null handle returns
SQLITE_OK and preserves the store and invoke frame. -/
theorem reactorPreparedCloseNull (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address helperAddress,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_close") =
        some ⟨"sqlite3_close", .func address⟩ ∧
      frame.module.funcs[295]? = some address ∧
      frame.module.funcs[296]? = some helperAddress ∧
      InvokeOk runtime address [.i32 0] ∧
      Steps P host (invoke runtime address [.i32 0]) ⟨runtime, {}, [constI32 0]⟩ := by
  obtain ⟨before, allocated, runtime, frame, _, prepared, alloc, sameFunctions, _, _, _, _, _, _,
    sameGlobals⟩ := reactorDirectPreparationWithGlobals
  have wrapper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 272) (fn := close) (d := closeType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have helper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 273) (fn := closeImpl) (d := closeImplType) alloc
    (by kernel_rfl) (by kernel_rfl)
  let address := before.funcs.length + 272
  let helperAddress := before.funcs.length + 273
  have slot : frame.module.funcs[295]? = some address := by
    simpa only [List.length_range] using wrapper.1
  have helperSlot : frame.module.funcs[296]? = some helperAddress := by
    simpa only [List.length_range] using helper.1
  have entry : runtime.funcs[address]? = some ⟨closeType, frame.module, .wasm close⟩ :=
    sameFunctions.symm ▸ wrapper.2
  have helperEntry : runtime.funcs[helperAddress]? = some ⟨closeImplType, frame.module, .wasm closeImpl⟩ :=
    sameFunctions.symm ▸ helper.2
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
  have source : sqlite.exports.find? (·.name == "sqlite3_close") =
      some ⟨"sqlite3_close", .func ⟨295⟩⟩ := by kernel_rfl
  have resolved : allocExport? frame.module ⟨"sqlite3_close", .func ⟨295⟩⟩ =
      some ⟨"sqlite3_close", .func address⟩ := by
    change (frame.module.funcs[295]?.map ExternAddr.func).map _ = _
    rw [slot]
    rfl
  have exported := findAllocated (allocatedExports alloc) source resolved
  exact ⟨runtime, frame, address, helperAddress, prepared, exported, slot, helperSlot,
    closeReturnsZero entry helperSlot helperEntry stackSlot stackEntry⟩

#print axioms reactorPreparedCloseNull

end SqliteWasm
