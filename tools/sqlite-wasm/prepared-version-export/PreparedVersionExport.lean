module

public import SqliteWasm.DirectPreparation
import SqliteWasm.VersionCheck
import SqliteWasm.ArtifactCheck
import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 65536

private theorem allocatedExports {H : Type} {s allocated : Store H} {m : Module} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref} {elements : List (List Ref)}
    (alloc : allocModule? s m imports globals tables elements = some (allocated, mi)) :
    m.exports.mapM (allocExport? mi) = some mi.exports := by
  obtain ⟨_, _, _, _, _, built, view, _⟩ := allocModule?_inv alloc
  rw [view]
  convert built using 2
  funext e
  unfold allocExport?
  cases e.index <;> rfl

private theorem exportPreservesName {mi : ModuleInst} {source : Export} {target : ExportInst}
    (resolved : allocExport? mi source = some target) : target.name = source.name := by
  unfold allocExport? at resolved
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp resolved
  rfl

private theorem findResolved {mi : ModuleInst} {name : String} {exports : List Export}
    {instances : List ExportInst} {source : Export} {target : ExportInst}
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
    have sameName := exportPreservesName head
    by_cases named : (e.name == name) = true
    · have sameSource : e = source := by simpa [List.find?_cons, named] using found
      have sameTarget : x = target := Option.some.inj (head.symm.trans (sameSource ▸ resolved))
      rw [List.find?_cons, sameName, named]
      exact congrArg some sameTarget
    · have later : es.find? (·.name == name) = some source := by
        simpa [List.find?_cons, named] using found
      simpa [List.find?_cons, sameName, named] using ih tail later

private def version : Func := (definedFunction? sqlite 289).get (by kernel_rfl)
private def versionType : DefType := ((allocTypes sqlite.types)[version.type.toNat]?).get (by kernel_rfl)

/-- The pinned reactor's actual prepared version export returns the pinned release
number with the original store. -/
theorem reactorPreparedVersionExport (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame address,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "sqlite3_libversion_number") =
        some ⟨"sqlite3_libversion_number", .func address⟩ ∧
      InvokeOk runtime address [] ∧
      Steps P host (invoke runtime address []) ⟨runtime, {}, [constI32 3054001]⟩ := by
  obtain ⟨before, allocated, runtime, frame, _, prep, alloc, sameFunctions, _, _, _, _, _, _⟩ :=
    reactorDirectPreparation
  let address := before.funcs.length + 266
  let fn : FuncInst Nat := ⟨versionType, frame.module, .wasm version⟩
  have pair := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 266) (fn := version) (d := versionType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have slot : frame.module.funcs[289]? = some address := by
    simpa only [List.length_range] using pair.1
  have entry : runtime.funcs[address]? = some fn := sameFunctions.symm ▸ pair.2
  have signature : Expand fn.type (.func .nil (.cons Ty.i32 .nil)) := by
    change Expand versionType (.func .nil (.cons Ty.i32 .nil))
    exact Expand.iff.mpr (by kernel_rfl)
  have source : sqlite.exports.find? (·.name == "sqlite3_libversion_number") =
      some ⟨"sqlite3_libversion_number", .func ⟨289⟩⟩ := by kernel_rfl
  have link : allocExport? frame.module ⟨"sqlite3_libversion_number", .func ⟨289⟩⟩ =
      some ⟨"sqlite3_libversion_number", .func address⟩ := by
    change (frame.module.funcs[289]?.map ExternAddr.func).map _ = _
    rw [slot]
    rfl
  have exported := findResolved (allocatedExports alloc) source link
  have body : version.body = [.intConst .i32 3054001] := by
    have old := version_body
    have selected : versionFunction? = some version := by kernel_rfl
    rw [selected] at old
    exact Option.some.inj old
  let callee := Frame.forCall frame.module [] version.locals
  have enter : Step P host (invoke runtime address [])
      ⟨runtime, {}, [.frame 1 callee [.label 1 [] [constI32 3054001]]]⟩ := by
    unfold invoke
    rw [entry]
    have invokeStep := Step.callRefFunc (P := P) (host := host) (f := ({} : Frame))
      (c := .callRefType fn.type) (vs := []) trivial entry signature rfl rfl
    rw [body] at invokeStep
    exact invokeStep
  have reveal : Step P host
      ⟨runtime, callee, [.label 1 [] [constI32 3054001]]⟩
      ⟨runtime, callee, [constI32 3054001]⟩ := Step.labelVals (vs := [.i32 3054001])
  have finish := (reveal.steps.frame (f := ({} : Frame)) (n := 1)).tail
    (Step.frameVals (vs := [.i32 3054001]) rfl)
  exact ⟨runtime, frame, address, prep, exported, ⟨fn, .nil, _, entry, signature, .nil⟩,
    enter.steps.trans finish⟩

#print axioms reactorPreparedVersionExport

end SqliteWasm
