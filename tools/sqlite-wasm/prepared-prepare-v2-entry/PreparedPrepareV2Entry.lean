module

public import SqliteWasm.DirectPreparation
public import SqliteWasmArtifactEntries
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

private def wrapperFn : Func := (definedFunction? sqlite 113).get (by kernel_rfl)
private def helperFn : Func := (definedFunction? sqlite 105).get (by kernel_rfl)
private def wrapperType : DefType := ((allocTypes sqlite.types)[wrapperFn.type.toNat]?).get (by kernel_rfl)
private def helperType : DefType := ((allocTypes sqlite.types)[helperFn.type.toNat]?).get (by kernel_rfl)

private theorem wrapperBody :
    wrapperFn.body = [.localGet ⟨0⟩, .localGet ⟨1⟩, .localGet ⟨2⟩,
      .intConst .i32 128, .intConst .i32 0, .localGet ⟨3⟩, .localGet ⟨4⟩, .call ⟨105⟩] := by
  kernel_rfl

private theorem forward {P : Profile} {host : HostSemantics Nat}
    {s : Store Nat} {mi : ModuleInst} {address helperAddress : Nat}
    (entry : s.funcs[address]? = some ⟨wrapperType, mi, .wasm wrapperFn⟩)
    (helperSlot : mi.funcs[105]? = some helperAddress)
    (helperEntry : s.funcs[helperAddress]? = some ⟨helperType, mi, .wasm helperFn⟩)
    (db sql nByte stmtOut tailOut : BitVec 32) :
    let args : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    InvokeOk s address args ∧
    Steps P host (invoke s address args) ⟨s, {}, [
      .frame 1 (Frame.forCall mi args wrapperFn.locals) [.label 1 [] [
        .frame 1 (Frame.forCall mi forwarded helperFn.locals) [.label 1 [] (expression helperFn.body)]
      ]]
    ]⟩ := by
  let args : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 stmtOut, .i32 tailOut]
  let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
    .i32 stmtOut, .i32 tailOut]
  let caller := Frame.forCall mi args wrapperFn.locals
  have sig : Expand wrapperType (.func
      (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32 .nil)))))
      (.cons Ty.i32 .nil)) := Expand.iff.mpr (by kernel_rfl)
  have helperSig : Expand helperType (.func
      (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32
        (.cons Ty.i32 (.cons Ty.i32 (.cons Ty.i32 .nil)))))))
      (.cons Ty.i32 .nil)) := Expand.iff.mpr (by kernel_rfl)
  have enter : Step P host (invoke s address args)
      ⟨s, {}, [.frame 1 caller [.label 1 [] (expression wrapperFn.body)]]⟩ := by
    unfold invoke
    rw [entry]
    exact Step.callRefFunc (c := .callRefType wrapperType) (vs := args)
      trivial entry sig rfl rfl
  have readLocal (index : LocalIdx) (value : Val)
      (lookup : caller.locals[index.toNat]? = some value) (operands : List Val) (rest : List Admin) :
      Steps P host ⟨s, caller, vals operands ++ [.plain (.localGet index)] ++ rest⟩
        ⟨s, caller, vals operands ++ [value.toAdmin] ++ rest⟩ :=
    (Step.variable (P := P) (host := host) (.localGet lookup)).steps.ctxtInstrs
  have callHelper := Step.call (P := P) (host := host) (f := caller) (x := ⟨105⟩)
    helperSlot helperEntry
  have enterHelper := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType helperType) (vs := forwarded) trivial helperEntry helperSig rfl rfl
  have wrapped : Steps P host ⟨s, caller, expression wrapperFn.body⟩
      ⟨s, caller, [.frame 1 (Frame.forCall mi forwarded helperFn.locals)
        [.label 1 [] (expression helperFn.body)]]⟩ := by
    rw [wrapperBody]
    refine (readLocal ⟨0⟩ (.i32 db) rfl [] _).trans ?_
    refine (readLocal ⟨1⟩ (.i32 sql) rfl [.i32 db] _).trans ?_
    refine (readLocal ⟨2⟩ (.i32 nByte) rfl [.i32 db, .i32 sql] _).trans ?_
    refine (readLocal ⟨3⟩ (.i32 stmtOut) rfl [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0]
      _).trans ?_
    refine (readLocal ⟨4⟩ (.i32 tailOut) rfl
      [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0, .i32 stmtOut] _).trans ?_
    exact (callHelper.steps.ctxtInstrs (vs := forwarded) (rest := [])).tail enterHelper
  exact ⟨⟨_, _, _, entry, sig,
    .cons (.num _) (.cons (.num _) (.cons (.num _) (.cons (.num _) (.cons (.num _) .nil))))⟩,
    enter.steps.trans ((wrapped.label (n := 1) (cont := [])).frame (f := {}) (n := 1))⟩

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

/-- The actual named SQLite wrapper forwards its arguments to the allocated
helper in the pinned prepared reactor. The final state is the entry to the
helper with the exact original store and the wrapper suspended below it. -/
theorem reactorPreparedPrepareV2Entry (P : Profile) (host : HostSemantics Nat)
    (db sql nByte stmtOut tailOut : BitVec 32) :
    let args : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 stmtOut, .i32 tailOut]
    let forwarded : List Val := [.i32 db, .i32 sql, .i32 nByte, .i32 128, .i32 0,
      .i32 stmtOut, .i32 tailOut]
    ∃ runtime frame address helperAddress wrapper helper wrapperTy helperTy,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_prepare_v2") =
        some ⟨"sqlite3_prepare_v2", .func address⟩ ∧
      frame.module.funcs[113]? = some address ∧
      frame.module.funcs[105]? = some helperAddress ∧
      definedFunction? sqlite 113 = some wrapper ∧
      definedFunction? sqlite 105 = some helper ∧
      runtime.funcs[address]? = some ⟨wrapperTy, frame.module, .wasm wrapper⟩ ∧
      runtime.funcs[helperAddress]? = some ⟨helperTy, frame.module, .wasm helper⟩ ∧
      InvokeOk runtime address args ∧
      Steps P host (invoke runtime address args) ⟨runtime, {}, [
        .frame 1 (Frame.forCall frame.module args wrapper.locals) [.label 1 [] [
          .frame 1 (Frame.forCall frame.module forwarded helper.locals) [.label 1 [] (expression helper.body)]
        ]]
      ]⟩ := by
  obtain ⟨before, _, runtime, frame, _, prepared, alloc, sameFunctions, _, _, _, _, _, _⟩ :=
    reactorDirectPreparation
  have wrapper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 90) (fn := wrapperFn) (d := wrapperType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have helper := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 82) (fn := helperFn) (d := helperType) alloc
    (by kernel_rfl) (by kernel_rfl)
  let address := before.funcs.length + 90
  let helperAddress := before.funcs.length + 82
  have slot : frame.module.funcs[113]? = some address := by
    simpa only [List.length_range] using wrapper.1
  have helperSlot : frame.module.funcs[105]? = some helperAddress := by
    simpa only [List.length_range] using helper.1
  have entry : runtime.funcs[address]? = some ⟨wrapperType, frame.module, .wasm wrapperFn⟩ :=
    sameFunctions.symm ▸ wrapper.2
  have helperEntry : runtime.funcs[helperAddress]? = some ⟨helperType, frame.module, .wasm helperFn⟩ :=
    sameFunctions.symm ▸ helper.2
  have source : sqlite.exports.find? (·.name == "sqlite3_prepare_v2") = some ⟨"sqlite3_prepare_v2", .func ⟨113⟩⟩ := by
    kernel_rfl
  have resolved : allocExport? frame.module ⟨"sqlite3_prepare_v2", .func ⟨113⟩⟩ =
      some ⟨"sqlite3_prepare_v2", .func address⟩ := by
    change (frame.module.funcs[113]?.map ExternAddr.func).map _ = _
    rw [slot]
    rfl
  have exported := findAllocated (allocatedExports alloc) source resolved
  have linkedWrapper : definedFunction? sqlite 113 = some wrapperFn := by kernel_rfl
  have linkedHelper : definedFunction? sqlite 105 = some helperFn := by kernel_rfl
  exact ⟨runtime, frame, address, helperAddress, wrapperFn, helperFn, wrapperType, helperType,
    prepared, exported, slot, helperSlot, linkedWrapper, linkedHelper, entry, helperEntry,
    forward entry helperSlot helperEntry db sql nByte stmtOut tailOut⟩

#print axioms reactorPreparedPrepareV2Entry

end SqliteWasm
