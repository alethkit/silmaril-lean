module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence

open Execution
open Execution.Runtime (Frame FuncAddr Value ModuleInst)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem core_frame_forCall (m : ModuleInst) (args : List Value) (locals : List NumType) :
    Core.Frame.forCall m.toCore (args.map Value.toCore) (locals.map Wasm.V1.ValType.toCore) =
      (⟨args ++ locals.map Value.zero, m⟩ : Frame).toCore :=
  Proofs.Core.frame_forCall m args locals

theorem wasm_entry_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame}
    {address : FuncAddr} {ty : Wasm.V1.FuncType} {m : Execution.Runtime.ModuleInst} {fn : Wasm.Func}
    {args : List Value} {dst : Core.Config H}
    (allocated : s.funcs[address.value]? = some ⟨ty.toDefType, m.toCore, .wasm fn⟩)
    (typed : args.map Value.type = ty.params) :
    Core.Step P noHost ⟨s, caller.toCore, coreValues args ++ [.ref (.func address.value), .callRefType ty.toDefType]⟩ dst ↔
      dst = ⟨s, caller.toCore, [.frame ty.results.length
        (Core.Frame.forCall m.toCore (args.map Value.toCore) fn.locals)
        [.label ty.results.length [] (Core.expression fn.body)]]⟩ :=
  Proofs.Core.wasm_entry_iff allocated typed

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    (g : V1Guard s caller site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller site :=
  Proofs.guard_to_lime g

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) : CoreGuard s.toCore caller site :=
  Proofs.guard_to_core g

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q :=
  Proofs.v1_to_lime s caller site q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) (q : State) :
    (limeConfig s caller site q).toCore = coreConfig s.toCore caller site q :=
  Proofs.lime_to_core g q

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : Site}
    {a b : State} (guard : CoreGuard s caller site) (edge : Edge site a b) :
    Core.Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) :=
  Proofs.Core.sound guard edge

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : Site}
    {a : State} {b : Core.Config H} (guard : CoreGuard s caller site) (ready : Admitted site a) :
    Core.Step P noHost (coreConfig s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = coreConfig s caller site out :=
  ⟨Proofs.Core.readback guard ready, fun ⟨_, move, eq⟩ => eq.symm ▸ core_sound guard move⟩

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    {a b : State} (g : LimeGuard s caller site) (edge : Edge site a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) :=
  Proofs.Lime1.sound g edge

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = limeConfig s caller site out :=
  ⟨Proofs.Lime1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ lime_sound g move⟩

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    {a b : State} (g : V1Guard s caller site) (edge : Edge site a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller site a) (v1Config s caller site b) :=
  Proofs.V1.sound g edge

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller site) (ready : Admitted site a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = v1Config s caller site out :=
  ⟨Proofs.V1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ v1_sound g move⟩

theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : Site}
    {a : State} {b : Core.Config H} (guard : CoreGuard s caller site) (ready : Admitted site a) :
    Core.Steps P noHost (coreConfig s caller site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = coreConfig s caller site out :=
  Proofs.run_iff (coreConfig s caller site) _ guard.typed (fun e => core_sound guard e)
    (fun h => core_step_iff guard h) ready

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State} {b : Wasm.Lime1.Execution.Config H}
    (guard : LimeGuard s caller site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s caller site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = limeConfig s caller site out :=
  Proofs.run_iff (limeConfig s caller site) _ guard.typed (fun e => lime_sound guard e)
    (fun h => lime_step_iff guard h) ready

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State} {b : Wasm.V1.Execution.Config H}
    (guard : V1Guard s caller site) (ready : Admitted site a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s caller site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = v1Config s caller site out :=
  Proofs.run_iff (v1Config s caller site) _ guard.typed (fun e => v1_sound guard e)
    (fun h => v1_step_iff guard h) ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence
