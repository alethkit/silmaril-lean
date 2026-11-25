module

public import Silmaril.Wasm.SingleThreaded.Determinism.Head

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence

open Execution
open Execution.Runtime (Frame)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem core_body_expression (p : Program) :
    Core.expression p.coreFunc.body = StraightLine.Sequence.coreCode p.site.body (.running [] p.code) :=
  Proofs.Core.body_expression p

theorem lime_body_expression (p : Program) :
    Wasm.Lime1.Execution.expression p.limeFunc.body = StraightLine.Sequence.limeCode p.site.body (.running [] p.code) :=
  Proofs.Lime1.body_expression p

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {p : Program}
    (g : V1Guard s caller p) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller p :=
  Proofs.guard_to_lime g

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    (g : LimeGuard s caller p) : CoreGuard s.toCore caller p :=
  Proofs.guard_to_core g

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State site) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q :=
  Proofs.v1_to_lime s caller site q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    (g : LimeGuard s caller p) (q : State p.site) :
    (limeConfig s caller p.site q).toCore = coreConfig s.toCore caller p.site q :=
  Proofs.lime_to_core g q

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {p : Program}
    {a b : State p.site} (g : CoreGuard s caller p) (edge : Edge p a b) :
    Core.Step P noHost (coreConfig s caller p.site a) (coreConfig s caller p.site b) :=
  Proofs.Core.sound g edge

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {p : Program}
    {a : State p.site} {b : Core.Config H} (g : CoreGuard s caller p) (ready : Admitted p.site a) :
    Core.Step P noHost (coreConfig s caller p.site a) b ↔
      ∃ out, Edge p a out ∧ b = coreConfig s caller p.site out :=
  ⟨Proofs.Core.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ core_sound g move⟩

theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {p : Program}
    {a : State p.site} {b : Core.Config H} (g : CoreGuard s caller p) (ready : Admitted p.site a) :
    Core.Steps P noHost (coreConfig s caller p.site a) b ↔
      ∃ out, Runs p a out ∧ Admitted p.site out ∧ b = coreConfig s caller p.site out :=
  Proofs.run_iff (coreConfig s caller p.site) _ g.typed g.body.typed
    (fun edge => core_sound g edge) (fun h => (core_step_iff g h).mp) ready

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    {a b : State p.site} (g : LimeGuard s caller p) (edge : Edge p a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller p.site a) (limeConfig s caller p.site b) :=
  Proofs.Lime1.sound g edge

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    {a : State p.site} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller p) (ready : Admitted p.site a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller p.site a) b ↔
      ∃ out, Edge p a out ∧ b = limeConfig s caller p.site out :=
  ⟨Proofs.Lime1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ lime_sound g move⟩

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    {a : State p.site} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller p) (ready : Admitted p.site a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s caller p.site a) b ↔
      ∃ out, Runs p a out ∧ Admitted p.site out ∧ b = limeConfig s caller p.site out :=
  Proofs.run_iff (limeConfig s caller p.site) _ g.typed g.body.typed
    (fun edge => lime_sound g edge) (fun h => (lime_step_iff g h).mp) ready

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {p : Program}
    {a b : State p.site} (g : V1Guard s caller p) (edge : Edge p a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller p.site a) (v1Config s caller p.site b) :=
  Proofs.V1.sound g edge

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {p : Program}
    {a : State p.site} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller p) (ready : Admitted p.site a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller p.site a) b ↔
      ∃ out, Edge p a out ∧ b = v1Config s caller p.site out :=
  ⟨Proofs.V1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ v1_sound g move⟩

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {p : Program}
    {a : State p.site} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller p) (ready : Admitted p.site a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s caller p.site a) b ↔
      ∃ out, Runs p a out ∧ Admitted p.site out ∧ b = v1Config s caller p.site out :=
  Proofs.run_iff (v1Config s caller p.site) _ g.typed g.body.typed
    (fun edge => v1_sound g edge) (fun h => (v1_step_iff g h).mp) ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence
