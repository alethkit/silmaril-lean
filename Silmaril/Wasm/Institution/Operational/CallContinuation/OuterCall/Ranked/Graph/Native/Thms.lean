module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.V1Guard

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution
open Execution.Runtime (Frame Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

/-- Exact native composition under the parent's function label and frame
when the child has entered its own frame. No bound on the child's code or nesting is needed. -/
theorem core_entered_child_iff {H : Type} {P : Profile} {s : Core.Store H} {caller parent child : Core.Frame}
    {n k : Nat} {saved : List Core.Val} {body rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost
      ⟨s, caller, [.frame n parent [.label n [] (Core.vals saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Core.Step P noHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (Core.vals saved ++ mid.code ++ rest)]]⟩ :=
  Proofs.core_entered_child_iff

open Wasm.Lime1.Execution in
/-- The same entered-child boundary for Lime1 preserves the pending suffix at
the parent's label, even on the step that delivers a trap. -/
theorem lime_entered_child_iff {H : Type} {s : Store H} {caller parent child : Frame}
    {n k : Nat} {saved : List Value} {body rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, caller, [.frame n parent [.label n [] (values saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (values saved ++ mid.code ++ rest)]]⟩ :=
  Proofs.lime_entered_child_iff

open Wasm.V1.Execution in
/-- Lift reflection of the child's V1 steps along the V1-to-Lime1 projection
through a suspended caller, using the same native context as Lime1. -/
theorem v1_entered_child_iff {H : Type} {s : Store H} {caller parent child : Frame}
    {n k : Nat} {saved : List Value} {body rest : List Admin} {dst : Config H}
    (reflectChild : ∀ out, Wasm.Lime1.Execution.Step CallFrame.limeNoHost
        (Config.toLime (⟨s, parent, [.frame k child body]⟩ : Config H)) out →
      ∃ mid, Step CallFrame.v1NoHost ⟨s, parent, [.frame k child body]⟩ mid ∧ mid.toLime = out) :
    Step CallFrame.v1NoHost
      ⟨s, caller, [.frame n parent [.label n [] (values saved ++ .frame k child body :: rest)]]⟩ dst ↔
      ∃ mid, Step CallFrame.v1NoHost ⟨s, parent, [.frame k child body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] (values saved ++ mid.code ++ rest)]]⟩ :=
  Proofs.v1_entered_child_iff reflectChild

section Core

variable {H : Type} {P : Profile} {s : Core.Store H} {program : Program}
  {caller : Frame} {target : CallTarget} {fn : Function}

/-- Decode any native Core successor of a guarded graph phase, including
administrative steps inside any number of entered children. -/
theorem core_step_iff (checked : program.check = true) (allocated : program.CoreAllocated s)
    (root : Root program caller target fn) {a : Phase} {b : Core.Config H} (ready : Admitted program fn a) :
    Core.Step P noHost (coreConfig s caller target a) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = coreConfig s caller target out :=
  Proofs.Core.step_iff checked allocated target.address rfl root ready

theorem core_run_iff (checked : program.check = true) (allocated : program.CoreAllocated s)
    (root : Root program caller target fn) {a : Phase} {b : Core.Config H} (ready : Admitted program fn a) :
    Core.Steps P noHost (coreConfig s caller target a) b ↔
      ∃ out, program.Runs checked target.address a out ∧ Admitted program fn out ∧ b = coreConfig s caller target out :=
  Proofs.run_iff root.found (coreConfig s caller target) _ (fun h => core_step_iff checked allocated root h) ready

end Core

section Lime1

variable {H : Type} {s : Wasm.Lime1.Execution.Store H} {program : Program}
  {caller : Frame} {target : CallTarget} {fn : Function}

theorem lime_step_iff (checked : program.check = true) (allocated : program.LimeAllocated s)
    (root : Root program caller target fn) {a : Phase} {b : Wasm.Lime1.Execution.Config H} (ready : Admitted program fn a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller target a) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = limeConfig s caller target out :=
  Proofs.Lime1.step_iff checked allocated target.address rfl root ready

theorem lime_run_iff (checked : program.check = true) (allocated : program.LimeAllocated s)
    (root : Root program caller target fn) {a : Phase} {b : Wasm.Lime1.Execution.Config H} (ready : Admitted program fn a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s caller target a) b ↔
      ∃ out, program.Runs checked target.address a out ∧ Admitted program fn out ∧ b = limeConfig s caller target out :=
  Proofs.run_iff root.found (limeConfig s caller target) _ (fun h => lime_step_iff checked allocated root h) ready

end Lime1

section V1

variable {H : Type} {s : Wasm.V1.Execution.Store H} {program : Program}
  {caller : Frame} {target : CallTarget} {fn : Function}

theorem v1_to_lime (s : Wasm.V1.Execution.Store H) (caller : Frame) (target : CallTarget) (q : Phase)
    (supported : q.supportsV1 = true) :
    (v1Config s caller target q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller target q :=
  Proofs.V1.config_to_lime s caller target q supported

/-- The graph-wide source and arity guard supplies V1 reflection at every registered
activation, including a child whose native step was read in Lime1. -/
theorem v1_reflect_lime_step (checked : program.checkV1 = true) (allocated : program.V1Allocated s)
    (root : Root program caller target fn) {a : Phase} {dst : Wasm.Lime1.Execution.Config H}
    (ready : Admitted program fn a) (supported : a.supportsV1 = true)
    (step : Wasm.Lime1.Execution.Step CallFrame.limeNoHost (v1Config s caller target a).toLime dst) :
    ∃ mid, Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller target a) mid ∧ mid.toLime = dst :=
  Proofs.V1.reflect_lime_step checked allocated root ready supported step

theorem v1_step_iff (checked : program.checkV1 = true) (allocated : program.V1Allocated s)
    (root : Root program caller target fn) {a : Phase} {b : Wasm.V1.Execution.Config H} (ready : Admitted program fn a) (supported : a.supportsV1 = true) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller target a) b ↔
      ∃ out, program.Edge (Bool.and_eq_true_iff.mp checked).1 target.address a out ∧ b = v1Config s caller target out :=
  Proofs.V1.step_iff checked allocated root ready supported

theorem v1_run_iff (checked : program.checkV1 = true) (allocated : program.V1Allocated s)
    (root : Root program caller target fn) {a : Phase} {b : Wasm.V1.Execution.Config H} (ready : Admitted program fn a) (supported : a.supportsV1 = true) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s caller target a) b ↔
      ∃ out, program.Runs (Bool.and_eq_true_iff.mp checked).1 target.address a out ∧
        Admitted program fn out ∧ b = v1Config s caller target out :=
  Proofs.run_iff_of_invariant root.found (v1Config s caller target) _
    (fun phase => phase.supportsV1 = true) (Proofs.edge_v1 checked target.address root.found)
    (fun h compatible => v1_step_iff checked allocated root h compatible) ready supported

end V1

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
