module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples.Defs
import Silmaril.Wasm.Logic.Core.Thms

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall

open Silmaril.MLIR.WasmSSA
open Silmaril.MLIR.WasmSSA.Examples (context selectDifference)
open Silmaril.MLIR.WasmSSA.ModuleCall.Examples
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Expand validate?_sound)

theorem coreModule_instantiates (P : Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) coreModule [] instantiated ∧ instantiated.code = [] := by
  have valid := validate?_sound (m := coreModule) (mt := checkedType) rfl
  refine ⟨instantiate?_sound (fun _ _ _ _ _ h => evalConst?_sound h) rfl ?_, rfl⟩
  exact ⟨checkedType.exports, checkedType.imports, valid, .nil⟩

private abbrev Ready (x y : BitVec 64) (store : Store Empty) (values : List Val) : Prop :=
  store = instantiated.store ∧ values = [.i64 x, .i64 y]

private abbrev Returns (x y : BitVec 64) (store : Store Empty) (values : List Val) : Prop :=
  store = instantiated.store ∧ values = [result x y]

private theorem leafSpec (P : Profile) (host : HostSemantics Empty) (x y : BitVec 64) :
    FuncSpec P host leafAddress (Ready x y) (fun _ _ => Returns x y) := by
  have fits : selectDifference.Fits := by decide
  let code := selectDifference.toWasm context ⟨0⟩ fits
  have signature : Expand leafInstance.type (Func.coreSignature Params .i64) := Expand.iff.mpr rfl
  refine FuncSpec.of_body (fi := leafInstance) (code := code)
    (fun _ _ h => h.1.symm ▸ rfl) rfl signature (fun _ _ h => by rw [h.2]; rfl) ?_
  rintro _ _ ⟨rfl, rfl⟩
  obtain ⟨_, run⟩ := selectDifference.toWasm_returns context ⟨0⟩ fits (args x y)
    leafInstance.module P host instantiated.store
  exact WP.steps run (wp_return ⟨[], [result x y], rfl, rfl, rfl, rfl⟩)

private theorem wrapperBody (P : Profile) (host : HostSemantics Empty) (x y : BitVec 64) :
    WP P host instantiated.store (Frame.forCall wrapperInstance.module [.i64 x, .i64 y] wrapperCode.locals)
      (expression wrapperCode.body) (funcPost P host 1 (Returns x y)) := by
  apply wp_exec₀ (is := [.localGet ⟨0⟩, .localGet ⟨1⟩])
    (rest := [.plain (.call leafIndex), .plain .return_])
  refine wp_call (vs := []) (args := [.i64 x, .i64 y]) (x := leafIndex) (a := leafAddress)
    rfl rfl (leafSpec P host x y) ⟨rfl, rfl⟩ ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact wp_return ⟨[], [result x y], rfl, rfl, rfl, rfl⟩

theorem invoke_export (P : Profile) (host : HostSemantics Empty) (x y : BitVec 64) :
    Steps P host (invoke instantiated.store wrapperAddress [.i64 x, .i64 y])
      ⟨instantiated.store, {}, vals [result x y]⟩ := by
  have signature : Expand wrapperInstance.type (Func.coreSignature Params .i64) := Expand.iff.mpr rfl
  obtain ⟨_, _, run, store, values⟩ := funcSpec_invoke_of_body
    (P := P) (host := host) (fi := wrapperInstance) (code := wrapperCode)
    (Pre := Ready x y) (Post := fun _ _ => Returns x y)
    (fun _ _ h => h.1.symm ▸ rfl) rfl signature (fun _ _ h => by rw [h.2]; rfl)
    (by rintro _ _ ⟨rfl, rfl⟩; exact wrapperBody P host x y) (a := wrapperAddress) ⟨rfl, rfl⟩
  simpa only [store, values] using run

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall
