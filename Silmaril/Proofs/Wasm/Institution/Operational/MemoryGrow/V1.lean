module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms
import Silmaril.Wasm.RuntimeMap.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs.V1

open Execution
open Execution.Runtime
open Wasm.V1.Execution

theorem sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) {q b : State} (edge : Edge m q b) :
    Step host (v1Config s f a m q) (v1Config s f a m b) := by
  cases invert edge with
  | grow delta bytes grown => exact .memoryGrow s f a m delta _ bytes lookup (.success bytes grown)
  | fail delta =>
    have reset : setMemory s a m = s := by simp [setMemory, set_current s.memories f lookup]
    have step := Step.memoryGrow (host := host) s f a m delta (-1) m.data lookup .failure
    cases m
    simp only [reset] at step
    exact step

private theorem config_injective (H : Type) : Function.Injective (Config.toLime (H := H)) := by
  rintro ⟨s, f, xs⟩ ⟨t, g, ys⟩ eq
  have stores := RuntimeMap.store_mapCode_injective Wasm.V1.Func.toLime_injective
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.store) eq)
  have frames : f = g := congrArg (fun c : Wasm.Lime1.Execution.Config H => c.frame) eq
  have codes := RuntimeMap.adminInstr_mapList_injective Wasm.V1.Instr.toLime_injective xs ys
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) eq)
  cases stores
  cases frames
  cases codes
  rfl

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) {q : State} {b : Config H}
    (step : Step host (v1Config s f a m q) b) :
    ∃ out, Edge m q out ∧ b = v1Config s f a m out := by
  have translated := step.toLime (Runtime.HostSemantics.compatible_mapCode Wasm.V1.Func.toLime host)
  rw [Proofs.v1_to_lime] at translated
  have mapped := (map_frameMemory s f).trans lookup
  obtain ⟨out, edge, eq⟩ := Proofs.Lime1.readback mapped translated
  exact ⟨out, edge, config_injective H (eq.trans (Proofs.v1_to_lime s f a m out).symm)⟩

end Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs.V1
