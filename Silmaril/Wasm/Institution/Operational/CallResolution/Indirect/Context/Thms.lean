module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context

open Execution
open CallContinuation.OuterCall.Ranked
open CallContinuation
open Wasm.SingleThreaded.Det (noHost)

theorem entered_admitted {call : Invocation} {program : Graph.Program}
    (checked : call.Checked program) : Graph.Admitted program call.callee call.entered :=
  Proofs.entered_admitted checked

theorem entered_frame_edge {program : Graph.Program} {address : Execution.Runtime.FuncAddr}
    {fn : Graph.Function} (found : program.lookup address = some fn)
    {a b : Graph.Phase} (live : a.LabelOutcome) (move : program.FrameEdge address a b) :
    b.LabelOutcome ∨ ∃ result, b = .done result :=
  Proofs.frame_entered found live move

theorem finite_run_iff_of_step {A C : Type} {edge : A → A → Prop} {native : C → C → Prop}
    (render : A → C) (step : ∀ a b, native (render a) b ↔ ∃ out, edge a out ∧ b = render out)
    {a : A} {b : C} :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, Relation.ReflTransGen edge a out ∧ b = render out := by
  simpa only [true_and] using
    (Proofs.lift_runs (fun _ => True) render (fun _ _ => trivial) (fun _ => step _ _) (a := a) (b := b) trivial)

theorem linked_runs {C : Type} {program : Graph.Program} {fn : Graph.Function}
    {address : Execution.Runtime.FuncAddr} (checked : program.checkDirect = true)
    (found : program.lookup address = some fn) (render : Graph.Phase → C) (native : C → C → Prop)
    (step : ∀ {a b}, Graph.Admitted program fn a → (∀ args, a ≠ .call args ∧ a ≠ .invoke args) →
      (native (render a) b ↔ ∃ out, program.FrameEdge address a out ∧ b = render out))
    {a : Graph.Phase} {b : C} (admitted : Graph.Admitted program fn a) (live : a.LabelOutcome) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, program.FrameRuns address a out ∧ Graph.Admitted program fn out ∧ b = render out :=
  Proofs.linked_runs checked found render native step admitted live

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}
  {call : Invocation} {program : Graph.Program} {rest : List Core.Admin}

/-- Core takes four steps through lowering, the table load, the nullable cast,
and entry by `call_ref`. Each step has an exact native successor. -/
theorem core_prefix_exact (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) :
    (call.corePrefix s rest).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.prefix_exact checked allocated tableFound

theorem core_entered_config :
    coreEntered s call.caller call.callee call.saved call.args rest = call.coreCallee s rest call.entered :=
  Proofs.Core.entered_config

theorem core_frame_shape {phase : Graph.Phase} (live : phase.LabelOutcome) :
    ∃ n f body, phase.render Graph.coreAdmin call.target = [Core.Admin.frame n f body] :=
  Proofs.Core.frame_shape live

theorem core_linked_frame_step_iff (checked : call.Checked program) (allocated : program.CoreLinksAllocated s)
    {phase : Graph.Phase} {dst : Core.Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Core.Step P noHost (call.coreCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.coreCallee s rest out :=
  Proofs.Core.linked_frame_step_iff checked allocated ready live

theorem core_frame_step_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {phase : Graph.Phase} {dst : Core.Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Core.Step P noHost (call.coreCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.coreCallee s rest out :=
  Proofs.Core.frame_step_iff checked allocated ready live

/-- Read back every finite endpoint through the handoff to the caller, including
intermediate recursive activations and each native trap discard. -/
theorem core_run_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat}
    (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) {dst : Core.Config H} :
    call.CoreRun P s rest dst ↔
      call.Run program rest (call.corePrefix s rest) (call.coreCallee s rest) (call.coreTrap s) dst :=
  Proofs.Core.run_iff checked allocated tableFound

theorem core_steps_of_run {dst : Core.Config H} (run : call.CoreRun P s rest dst) :
    Core.Steps P noHost
      (coreConfig s call.caller call.site call.selector (call.saved ++ call.args) rest .start) dst :=
  Proofs.Core.steps_of_run run

theorem core_handoff_stops (result : Nested.Result) (dst : Core.Config H) :
    ¬ call.coreFrameStep P rest (call.coreCallee s rest (.done result)) dst :=
  Proofs.Core.stopped result dst

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H} {call : Invocation}
  {program : Graph.Program} {rest : List Admin}

/-- Lime1 resolves in one step and enters the callee in the next step. -/
theorem lime_prefix_exact (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) :
    (call.limePrefix s rest).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.prefix_exact checked allocated tableFound

theorem lime_entered_config :
    limeEntered s call.caller call.callee call.saved call.args rest = call.limeCallee s rest call.entered :=
  Proofs.Lime1.entered_config

theorem lime_frame_shape {phase : Graph.Phase} (live : phase.LabelOutcome) :
    ∃ n f body, phase.render Graph.limeAdmin call.target = [Execution.Runtime.AdminInstr.frame n f body] :=
  Proofs.Lime1.frame_shape live

theorem lime_linked_frame_step_iff (checked : call.Checked program) (allocated : program.LimeLinksAllocated s)
    {phase : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Step CallFrame.limeNoHost (call.limeCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.limeCallee s rest out :=
  Proofs.Lime1.linked_frame_step_iff checked allocated ready live

theorem lime_frame_step_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    {phase : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Step CallFrame.limeNoHost (call.limeCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.limeCallee s rest out :=
  Proofs.Lime1.frame_step_iff checked allocated ready live

theorem lime_run_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) {dst : Config H} :
    call.LimeRun s rest dst ↔
      call.Run program rest (call.limePrefix s rest) (call.limeCallee s rest) (call.limeTrap s) dst :=
  Proofs.Lime1.run_iff checked allocated tableFound

theorem lime_steps_of_run {dst : Config H} (run : call.LimeRun s rest dst) :
    Steps CallFrame.limeNoHost
      (limeSource s call.caller call.site call.selector (call.saved ++ call.args) rest) dst :=
  Proofs.Lime1.steps_of_run run

theorem lime_handoff_stops (result : Nested.Result) (dst : Config H) :
    ¬ call.limeFrameStep rest (call.limeCallee s rest (.done result)) dst :=
  Proofs.Lime1.stopped result dst

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context
