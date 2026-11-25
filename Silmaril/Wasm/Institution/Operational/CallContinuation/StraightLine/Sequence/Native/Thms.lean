module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence

open Execution
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {site : Site}
    (g : V1Guard s site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) site :=
  Proofs.guard_to_lime g

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    (g : LimeGuard s site) : CoreGuard s.toCore site :=
  Proofs.guard_to_core g

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (site : Site) (q : State site) :
    (v1Config s site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) site q :=
  Proofs.v1_to_lime s site q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    (g : LimeGuard s site) (q : State site) :
    (limeConfig s site q).toCore = coreConfig s.toCore site q :=
  Proofs.lime_to_core g q

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {site : Site}
    {a b : State site} (guard : CoreGuard s site) (edge : Edge site a b) :
    Core.Step P noHost (coreConfig s site a) (coreConfig s site b) :=
  Proofs.Core.sound guard edge

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {site : Site}
    {a : State site} {b : Core.Config H} (guard : CoreGuard s site) (ready : Admitted site a) :
    Core.Step P noHost (coreConfig s site a) b ↔
      ∃ out, Edge site a out ∧ b = coreConfig s site out :=
  ⟨Proofs.Core.readback guard ready, fun ⟨_, move, eq⟩ => eq.symm ▸ core_sound guard move⟩

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    {a b : State site} (g : LimeGuard s site) (edge : Edge site a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s site a) (limeConfig s site b) :=
  Proofs.Lime1.sound g edge

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    {a : State site} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s site a) b ↔
      ∃ out, Edge site a out ∧ b = limeConfig s site out :=
  ⟨Proofs.Lime1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ lime_sound g move⟩

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {site : Site}
    {a b : State site} (g : V1Guard s site) (edge : Edge site a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s site a) (v1Config s site b) :=
  Proofs.V1.sound g edge

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {site : Site}
    {a : State site} {b : Wasm.V1.Execution.Config H} (g : V1Guard s site) (ready : Admitted site a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s site a) b ↔
      ∃ out, Edge site a out ∧ b = v1Config s site out :=
  ⟨Proofs.V1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ v1_sound g move⟩

theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {site : Site}
    {a : State site} {b : Core.Config H} (guard : CoreGuard s site) (ready : Admitted site a) :
    Core.Steps P noHost (coreConfig s site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = coreConfig s site out :=
  Proofs.run_iff (coreConfig s site) _ guard.typed (fun e => core_sound guard e)
    (fun h step => (core_step_iff guard h).mp step) ready

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {site : Site}
    {a : State site} {b : Wasm.Lime1.Execution.Config H}
    (guard : LimeGuard s site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = limeConfig s site out :=
  Proofs.run_iff (limeConfig s site) _ guard.typed (fun e => lime_sound guard e)
    (fun h step => (lime_step_iff guard h).mp step) ready

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {site : Site}
    {a : State site} {b : Wasm.V1.Execution.Config H}
    (guard : V1Guard s site) (ready : Admitted site a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = v1Config s site out :=
  Proofs.run_iff (v1Config s site) _ guard.typed (fun e => v1_sound guard e)
    (fun h step => (v1_step_iff guard h).mp step) ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence
