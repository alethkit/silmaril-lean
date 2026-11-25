module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Defs
public import Silmaril.Wasm.Institution.Operational.BranchExit.Thms
import Silmaril.Wasm.Versions.Thms
import Silmaril.Wasm.RuntimeMap.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame Value)

theorem sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {ty : Option NumType} {a b : State} (edge : Edge ty a b) :
    Step host (v1Config s f ty a) (v1Config s f ty b) := by
  cases invert edge with
  | cross n below payload =>
    have lowered : lowerLabel (⟨1⟩ : LabelIdx) = ⟨0⟩ := by decide
    simpa only [v1Config, v1Code, List.append_nil, lowered] using
      (Step.label (Step.pure (host := host) s f (.labelBranchOuter n [] (below ++ payload) [] ⟨1⟩
        (by decide))) ty.toList.length [])
  | finish below payload typed =>
    have arity : payload.length = ty.toList.length := by simpa using congrArg List.length typed
    simpa only [v1Config, v1Code, values_append, List.append_nil, expression, List.map_nil] using
      (Step.pure (host := host) s f (.labelBranch ty.toList.length [] below payload [] arity))

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

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {ty : Option NumType} {a : State} {b : Config H}
    (guard : Admitted ty a) (step : Step host (v1Config s f ty a) b) :
    ∃ out, Edge ty a out ∧ b = v1Config s f ty out := by
  have translated := step.toLime (target := fun _ _ _ _ => True) (fun _ _ _ _ _ => trivial)
  rw [Proofs.v1_to_lime] at translated
  obtain ⟨out, edge, eq⟩ := Proofs.Lime1.readback guard translated
  exact ⟨out, edge, config_injective H (eq.trans (Proofs.v1_to_lime s f ty out).symm)⟩

end Silmaril.Wasm.Institution.Operational.BranchExit.Proofs.V1
