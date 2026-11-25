module

public import SqliteWasm.DirectPreparation
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536

private def free : Func := (definedFunction? sqlite 1546).get (by kernel_rfl)
private def freeImpl : Func := (definedFunction? sqlite 1547).get (by kernel_rfl)
private def freeType : DefType := ((allocTypes sqlite.types)[free.type.toNat]?).get (by kernel_rfl)
private def freeImplType : DefType := ((allocTypes sqlite.types)[freeImpl.type.toNat]?).get (by kernel_rfl)

private def nullGuard : List Instr :=
  [.localGet ⟨0⟩, .intTestOp .i32 .eqz, .brIf ⟨0⟩]

private def allocatorCode : List Instr :=
  match (freeImpl.body : List Instr) with
  | [Instr.block .empty body] => body.drop 3
  | _ => []

private theorem wrapperBody : free.body = [.localGet ⟨0⟩, .call ⟨1547⟩] := by
  kernel_rfl

private theorem implBody : freeImpl.body = [.block .empty (nullGuard ++ allocatorCode)] := by
  kernel_rfl

private theorem implReturns {P : Profile} {host : HostSemantics Nat} {s : Store Nat}
    {mi : ModuleInst} :
    let frame := Frame.forCall mi [.i32 0] freeImpl.locals
    Steps P host ⟨s, frame, expression freeImpl.body⟩ ⟨s, frame, []⟩ := by
  let frame := Frame.forCall mi [.i32 0] freeImpl.locals
  have get : Step P host ⟨s, frame, [.plain (.localGet ⟨0⟩)]⟩ ⟨s, frame, [constI32 0]⟩ :=
    .variable (.localGet rfl)
  have test : Step P host ⟨s, frame, [constI32 0, .plain (.intTestOp .i32 .eqz)]⟩
      ⟨s, frame, [constI32 1]⟩ :=
    .numeric (.intTestOp (t := .i32) (op := .eqz) (x := 0))
  have branch : Step P host ⟨s, frame, [constI32 1, .plain (.brIf ⟨0⟩)]⟩
      ⟨s, frame, [.plain (.br ⟨0⟩)]⟩ := Step.brIfTrue (by decide)
  have guard : Steps P host ⟨s, frame, expression (nullGuard ++ allocatorCode)⟩
      ⟨s, frame, [.plain (.br ⟨0⟩)] ++ expression allocatorCode⟩ := by
    refine (get.steps.ctxtInstrs (vs := []) (rest :=
      [.plain (.intTestOp .i32 .eqz), .plain (.brIf ⟨0⟩)] ++ expression allocatorCode)).trans ?_
    refine (test.steps.ctxtInstrs (vs := []) (rest :=
      [.plain (.brIf ⟨0⟩)] ++ expression allocatorCode)).trans ?_
    exact branch.steps.ctxtInstrs (vs := []) (rest := expression allocatorCode)
  have enter : Step P host ⟨s, frame, expression [.block .empty (nullGuard ++ allocatorCode)]⟩
      ⟨s, frame, [.label 0 [] (expression (nullGuard ++ allocatorCode))]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  change Steps P host ⟨s, frame, expression freeImpl.body⟩ ⟨s, frame, []⟩
  rw [implBody]
  exact (enter.steps.trans (guard.label (n := 0) (cont := []))).tail
    (Step.brLabelZero (vs' := []) (vs := []) rfl rfl)

private theorem returnInFrame {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {caller frame : Frame} {body : List Admin}
    (run : Steps P host ⟨s, frame, body⟩ ⟨s, frame, []⟩) :
    Steps P host ⟨s, caller, [.frame 0 frame [.label 0 [] body]]⟩ ⟨s, caller, []⟩ := by
  have label : Steps P host ⟨s, frame, [.label 0 [] body]⟩ ⟨s, frame, []⟩ :=
    (run.label (n := 0) (cont := [])).tail (Step.labelVals (vs := []))
  exact (label.frame (f := caller) (n := 0)).tail (Step.frameVals (vs := []) rfl)

private theorem freeReturns {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {mi : ModuleInst} {address helperAddress : Nat}
    (entry : s.funcs[address]? = some ⟨freeType, mi, .wasm free⟩)
    (helperSlot : mi.funcs[1547]? = some helperAddress)
    (helperEntry : s.funcs[helperAddress]? = some ⟨freeImplType, mi, .wasm freeImpl⟩) :
    InvokeOk s address [.i32 0] ∧ Steps P host (invoke s address [.i32 0]) ⟨s, {}, []⟩ := by
  have signature : Expand freeType (.func (.cons Ty.i32 .nil) .nil) :=
    Expand.iff.mpr (by kernel_rfl)
  have helperSignature : Expand freeImplType (.func (.cons Ty.i32 .nil) .nil) :=
    Expand.iff.mpr (by kernel_rfl)
  let caller := Frame.forCall mi [.i32 0] free.locals
  have enter : Step P host (invoke s address [.i32 0])
      ⟨s, {}, [.frame 0 caller [.label 0 [] (expression free.body)]]⟩ := by
    unfold invoke
    rw [entry]
    exact Step.callRefFunc (c := .callRefType freeType) (vs := [.i32 0])
      trivial entry signature rfl rfl
  have get : Step P host ⟨s, caller, [.plain (.localGet ⟨0⟩)]⟩ ⟨s, caller, [constI32 0]⟩ :=
    .variable (.localGet rfl)
  have helperCall := Step.call (P := P) (host := host) (f := caller) (x := ⟨1547⟩)
    helperSlot helperEntry
  have enterHelper := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType freeImplType) (vs := [.i32 0]) trivial helperEntry helperSignature rfl rfl
  have wrapped : Steps P host ⟨s, caller, expression free.body⟩ ⟨s, caller, []⟩ := by
    rw [wrapperBody]
    refine (get.steps.ctxtInstrs (vs := []) (rest := [.plain (.call ⟨1547⟩)])).trans ?_
    refine ((helperCall.steps.ctxtInstrs (vs := [.i32 0]) (rest := [])).tail enterHelper).trans ?_
    exact returnInFrame (implReturns (mi := mi))
  exact ⟨⟨_, .cons Ty.i32 .nil, .nil, entry, signature, .cons (.num _) .nil⟩,
    enter.steps.trans (returnInFrame wrapped)⟩

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

/-- The actual named free export accepts the null pointer in the directly prepared
reactor and returns no values with its original store and invoke frame. -/
theorem reactorPreparedFreeNull (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address helperAddress,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "free") = some ⟨"free", .func address⟩ ∧
      frame.module.funcs[1546]? = some address ∧
      frame.module.funcs[1547]? = some helperAddress ∧
      InvokeOk runtime address [.i32 0] ∧
      Steps P host (invoke runtime address [.i32 0]) ⟨runtime, {}, []⟩ := by
  obtain ⟨before, _, runtime, frame, _, prepared, alloc, sameFunctions, _, _, _, _, _, _⟩ :=
    reactorDirectPreparation
  have wrapper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 1523) (fn := free) (d := freeType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have helper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 1524) (fn := freeImpl) (d := freeImplType) alloc
    (by kernel_rfl) (by kernel_rfl)
  let address := before.funcs.length + 1523
  let helperAddress := before.funcs.length + 1524
  have slot : frame.module.funcs[1546]? = some address := by
    simpa only [List.length_range] using wrapper.1
  have helperSlot : frame.module.funcs[1547]? = some helperAddress := by
    simpa only [List.length_range] using helper.1
  have entry : runtime.funcs[address]? = some ⟨freeType, frame.module, .wasm free⟩ :=
    sameFunctions.symm ▸ wrapper.2
  have helperEntry : runtime.funcs[helperAddress]? = some ⟨freeImplType, frame.module, .wasm freeImpl⟩ :=
    sameFunctions.symm ▸ helper.2
  have source : sqlite.exports.find? (·.name == "free") = some ⟨"free", .func ⟨1546⟩⟩ := by
    kernel_rfl
  have resolved : allocExport? frame.module ⟨"free", .func ⟨1546⟩⟩ =
      some ⟨"free", .func address⟩ := by
    change (frame.module.funcs[1546]?.map ExternAddr.func).map _ = _
    rw [slot]
    rfl
  have exported := findAllocated (allocatedExports alloc) source resolved
  exact ⟨runtime, frame, address, helperAddress, prepared, exported, slot, helperSlot,
    freeReturns entry helperSlot helperEntry⟩

#print axioms reactorPreparedFreeNull

end SqliteWasm
