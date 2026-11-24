module

public import Silmaril.Wasm.Institution.DirectLiftTerminal.Defs
public import Silmaril.Wasm.Institution.Operational.Thms
import Cslib.Foundations.Semantics.LTS.Relation
import Silmaril.Wasm.Component.Reference.DirectLift.Init.Thms

public section

namespace Silmaril.Proofs.Wasm.Institution.DirectLiftTerminal

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.DirectLift
open Silmaril.Wasm.Institution.DirectLiftTerminal
open Silmaril.Logic.Operational (Runs Signature WasmShape)
open Silmaril.Wasm.Institution.Operational (shape system encode decode decode_encode step_iff)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

theorem reaches_iff {P : Profile} {x : SimpleExport} (model : ComponentModel P x)
    (out : CallOutcome) (store : Store Nat) :
    model.reaches out store ↔ coreReaches P x model.reduct out store := by
  have init := (DirectWire.instantiates_iff (prof := model.profile) model.prepared).2
    ⟨rfl, rfl, rfl⟩
  have named : model.wire.exportMap.lookup x.name = some (⟨0⟩ : FuncId) := by
    simp [model.named, DirectWire.exportMap]
  exact DirectWire.terminalObservationIff model.prepared model.boundary model.signature init named

private theorem steps_iff_runs {H : Type} (P : Profile) (host : HostSemantics H)
    (start final : Config H) :
    Steps P host start final ↔
      ∃ labels : List Unit, Runs (system P host).model (encode start) labels (encode final) := by
  let lts := Signature.toLTS (S := WasmShape.signatures.obj (shape H)) (system P host).model
  change Steps P host start final ↔ lts.CanReach (encode start) (encode final)
  rw [← Cslib.LTS.reflTransGen_unlabelledTr_iff lts]
  constructor
  · intro steps
    exact Relation.ReflTransGen.lift (p := lts.UnlabelledTr) encode
      (fun a b edge => ⟨(), (step_iff P host a b).2 edge⟩) _ _ steps
  · intro path
    have steps := Relation.ReflTransGen.lift (r := lts.UnlabelledTr) (p := Step P host) decode
      (fun _ _ ⟨_, edge⟩ => edge) _ _ path
    change Steps P host (decode (encode start)) (decode (encode final)) at steps
    simpa only [decode_encode] using steps

theorem operationalReaches_iff {P : Profile} {x : SimpleExport} (model : ComponentModel P x)
    (out : CallOutcome) (store : Store Nat) :
    model.reaches out store ↔
      ∃ (final : Config Nat) (result : Result) (labels : List Unit),
        Runs (system P (Det.noHost : HostSemantics Nat)).model
          (encode model.reduct) labels (encode final) ∧
        final.code = result.toAdmin ∧ Reports x out result ∧ store = final.store := by
  rw [reaches_iff, coreReaches]
  constructor
  · rintro ⟨final, result, ⟨steps, terminal⟩, reports, storeEq⟩
    obtain ⟨labels, run⟩ := (steps_iff_runs P Det.noHost model.reduct final).1 steps
    exact ⟨final, result, labels, run, terminal, reports, storeEq⟩
  · rintro ⟨final, result, labels, run, terminal, reports, storeEq⟩
    exact ⟨final, result, ⟨(steps_iff_runs P Det.noHost model.reduct final).2 ⟨labels, run⟩,
      terminal⟩, reports, storeEq⟩

end Silmaril.Proofs.Wasm.Institution.DirectLiftTerminal
