module

public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source

open Execution
open Execution.Runtime (Frame)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem Body.v1Func_toLime {decl : Declaration} (body : Body decl) : body.v1Func.toLime = body.limeFunc :=
  Proofs.func_to_lime body

theorem Body.limeFunc_toCore {decl : Declaration} (body : Body decl) : body.limeFunc.toCore = body.coreFunc :=
  Proofs.func_to_core body

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {call : Invocation}
    (g : V1Guard s caller call) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller call :=
  Proofs.guard_to_lime g

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    (g : LimeGuard s caller call) : CoreGuard s.toCore caller call :=
  Proofs.guard_to_core g

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (call : Invocation) (q : State call) :
    (v1Config s caller call q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller call q :=
  Proofs.v1_to_lime s caller call q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    (g : LimeGuard s caller call) (q : State call) :
    (limeConfig s caller call q).toCore = coreConfig s.toCore caller call q :=
  Proofs.lime_to_core g q

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {call : Invocation}
    {a b : State call} (g : CoreGuard s caller call) (edge : Edge call a b) :
    Core.Step P noHost (coreConfig s caller call a) (coreConfig s caller call b) :=
  Proofs.Core.sound g edge

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {call : Invocation}
    {a : State call} {b : Core.Config H} (g : CoreGuard s caller call) (ready : Admitted a) :
    Core.Step P noHost (coreConfig s caller call a) b ↔
      ∃ out, Edge call a out ∧ b = coreConfig s caller call out :=
  ⟨Proofs.Core.readback g ready, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound g edge⟩

theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {call : Invocation}
    {a : State call} {b : Core.Config H} (g : CoreGuard s caller call) (ready : Admitted a) :
    Core.Steps P noHost (coreConfig s caller call a) b ↔
      ∃ out, Runs call a out ∧ Admitted out ∧ b = coreConfig s caller call out :=
  Proofs.run_iff (coreConfig s caller call) _ g.typed g.body.invocation.typed g.body.invocation.body.typed
    g.body.continuation.typed (fun e => core_sound g e) (fun h => (core_step_iff g h).mp) ready

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    {a b : State call} (g : LimeGuard s caller call) (edge : Edge call a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller call a) (limeConfig s caller call b) :=
  Proofs.Lime1.sound g edge

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    {a : State call} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller call) (ready : Admitted a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller call a) b ↔
      ∃ out, Edge call a out ∧ b = limeConfig s caller call out :=
  ⟨Proofs.Lime1.readback g ready, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound g edge⟩

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    {a : State call} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller call) (ready : Admitted a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s caller call a) b ↔
      ∃ out, Runs call a out ∧ Admitted out ∧ b = limeConfig s caller call out :=
  Proofs.run_iff (limeConfig s caller call) _ g.typed g.body.invocation.typed g.body.invocation.body.typed
    g.body.continuation.typed (fun e => lime_sound g e) (fun h => (lime_step_iff g h).mp) ready

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {call : Invocation}
    {a b : State call} (g : V1Guard s caller call) (edge : Edge call a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller call a) (v1Config s caller call b) :=
  Proofs.V1.sound g edge

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {call : Invocation}
    {a : State call} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller call) (ready : Admitted a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller call a) b ↔
      ∃ out, Edge call a out ∧ b = v1Config s caller call out :=
  ⟨Proofs.V1.readback g ready, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound g edge⟩

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {call : Invocation}
    {a : State call} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller call) (ready : Admitted a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s caller call a) b ↔
      ∃ out, Runs call a out ∧ Admitted out ∧ b = v1Config s caller call out :=
  Proofs.run_iff (v1Config s caller call) _ g.typed g.body.invocation.typed g.body.invocation.body.typed
    g.body.continuation.typed (fun e => v1_sound g e) (fun h => (v1_step_iff g h).mp) ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source
