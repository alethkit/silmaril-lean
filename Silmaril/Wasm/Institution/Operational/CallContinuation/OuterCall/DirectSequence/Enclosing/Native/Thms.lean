module

public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open Execution
open StraightLine
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {ctx : Context} {p : Program}
    (g : V1Guard s ctx p) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) ctx p :=
  ⟨DirectSequence.guard_to_lime g.invocation, Sequence.guard_to_lime g.continuation⟩

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    (g : LimeGuard s ctx p) : CoreGuard s.toCore ctx p :=
  ⟨DirectSequence.guard_to_core g.invocation, Sequence.guard_to_core g.continuation⟩

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (ctx : Context) (site : Site) (q : State ctx site) :
    (v1Config s ctx site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) ctx site q :=
  Proofs.v1_to_lime s ctx site q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    (g : LimeGuard s ctx p) (q : State ctx p.site) :
    (limeConfig s ctx p.site q).toCore = coreConfig s.toCore ctx p.site q :=
  Proofs.lime_to_core g q

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {ctx : Context} {p : Program}
    {a b : State ctx p.site} (g : CoreGuard s ctx p) (edge : Edge ctx p a b) :
    Core.Step P noHost (coreConfig s ctx p.site a) (coreConfig s ctx p.site b) :=
  Proofs.Core.sound g edge

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {b : Core.Config H} (g : CoreGuard s ctx p) (ready : Admitted a) :
    Core.Step P noHost (coreConfig s ctx p.site a) b ↔
      ∃ out, Edge ctx p a out ∧ b = coreConfig s ctx p.site out :=
  ⟨Proofs.Core.readback g ready, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound g edge⟩

theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {b : Core.Config H} (g : CoreGuard s ctx p) (typed : ctx.Typed p) (ready : Admitted a) :
    Core.Steps P noHost (coreConfig s ctx p.site a) b ↔
      ∃ out, Runs ctx p a out ∧ Admitted out ∧ b = coreConfig s ctx p.site out :=
  Proofs.run_iff (coreConfig s ctx p.site) _ typed g.invocation.typed g.invocation.body.typed g.continuation.typed (fun e => core_sound g e)
    (fun h => (core_step_iff g h).mp) ready

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    {a b : State ctx p.site} (g : LimeGuard s ctx p) (edge : Edge ctx p a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s ctx p.site a) (limeConfig s ctx p.site b) :=
  Proofs.Lime1.sound g edge

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s ctx p) (ready : Admitted a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s ctx p.site a) b ↔
      ∃ out, Edge ctx p a out ∧ b = limeConfig s ctx p.site out :=
  ⟨Proofs.Lime1.readback g ready, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound g edge⟩

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s ctx p) (typed : ctx.Typed p) (ready : Admitted a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s ctx p.site a) b ↔
      ∃ out, Runs ctx p a out ∧ Admitted out ∧ b = limeConfig s ctx p.site out :=
  Proofs.run_iff (limeConfig s ctx p.site) _ typed g.invocation.typed g.invocation.body.typed g.continuation.typed (fun e => lime_sound g e)
    (fun h => (lime_step_iff g h).mp) ready

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {ctx : Context} {p : Program}
    {a b : State ctx p.site} (g : V1Guard s ctx p) (edge : Edge ctx p a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s ctx p.site a) (v1Config s ctx p.site b) :=
  Proofs.V1.sound g edge

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {b : Wasm.V1.Execution.Config H} (g : V1Guard s ctx p) (ready : Admitted a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s ctx p.site a) b ↔
      ∃ out, Edge ctx p a out ∧ b = v1Config s ctx p.site out :=
  ⟨Proofs.V1.readback g ready, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound g edge⟩

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {b : Wasm.V1.Execution.Config H} (g : V1Guard s ctx p) (typed : ctx.Typed p) (ready : Admitted a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s ctx p.site a) b ↔
      ∃ out, Runs ctx p a out ∧ Admitted out ∧ b = v1Config s ctx p.site out :=
  Proofs.run_iff (v1Config s ctx p.site) _ typed g.invocation.typed g.invocation.body.typed g.continuation.typed (fun e => v1_sound g e)
    (fun h => (v1_step_iff g h).mp) ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
