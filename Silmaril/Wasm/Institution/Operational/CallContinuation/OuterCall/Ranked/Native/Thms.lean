module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked

open Execution
open Execution.Runtime (Frame)
open DirectSequence.Enclosing.Framed
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

-- The native guards bind declarations to typed bodies at allocated addresses.
-- The rank check certifies the direct targets in those same bodies.
theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Frame} {call : Source.Invocation}
    {table : Table} (check : table.checkInvocation call = true) (guard : Source.CoreGuard s caller call)
    {a : Source.State call} {b : Core.Config H} (ready : Source.Admitted a) :
    Core.Steps P noHost (Source.coreConfig s caller call a) b ↔
      ∃ out, Source.Runs call a out ∧ Source.Admitted out ∧ b = Source.coreConfig s caller call out ∧
        table.Nesting (frames out) := by
  simpa only [table.nesting_of_check check, and_true] using Source.core_run_iff guard ready

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Source.Invocation}
    {table : Table} (check : table.checkInvocation call = true) (guard : Source.LimeGuard s caller call)
    {a : Source.State call} {b : Wasm.Lime1.Execution.Config H} (ready : Source.Admitted a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (Source.limeConfig s caller call a) b ↔
      ∃ out, Source.Runs call a out ∧ Source.Admitted out ∧ b = Source.limeConfig s caller call out ∧
        table.Nesting (frames out) := by
  simpa only [table.nesting_of_check check, and_true] using Source.lime_run_iff guard ready

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {call : Source.Invocation}
    {table : Table} (check : table.checkInvocation call = true) (guard : Source.V1Guard s caller call)
    {a : Source.State call} {b : Wasm.V1.Execution.Config H} (ready : Source.Admitted a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (Source.v1Config s caller call a) b ↔
      ∃ out, Source.Runs call a out ∧ Source.Admitted out ∧ b = Source.v1Config s caller call out ∧
        table.Nesting (frames out) := by
  simpa only [table.nesting_of_check check, and_true] using Source.v1_run_iff guard ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
