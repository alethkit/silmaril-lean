module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Code
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)

private theorem enter_iff {H : Type} {s : Store H} {caller : Frame}
    {call : Invocation} {dst : Config H} (g : LimeGuard s caller call) :
    Step CallFrame.limeNoHost (limeConfig s caller call .invoke) dst ↔
      dst = limeConfig s caller call (.framed call.start) := by
  have count : call.args.length = call.target.declaration.type.params.length := by
    simpa [Declaration.type] using congrArg List.length g.typed.args
  have enter := CallFrame.lime_invoke_wasm_exact (caller := caller) (dst := dst) g.allocated count
  rw [lime_expression] at enter
  exact enter

theorem sound {H : Type} {s : Store H} {caller : Frame} {call : Invocation}
    {a b : State call} (g : LimeGuard s caller call) (edge : Edge call a b) :
    Step CallFrame.limeNoHost (limeConfig s caller call a) (limeConfig s caller call b) := by
  cases invert edge with
  | framed move => exact Framed.lime_sound g.body move
  | ground rule =>
    cases rule with
    | resolve => exact (Computed.lime_direct_call_iff g.resolves).mpr rfl
    | enter => exact (enter_iff g).mpr rfl

theorem readback {H : Type} {s : Store H} {caller : Frame} {call : Invocation}
    {a : State call} {dst : Config H} (g : LimeGuard s caller call) (ready : Admitted a)
    (step : Step CallFrame.limeNoHost (limeConfig s caller call a) dst) :
    ∃ out, Edge call a out ∧ dst = limeConfig s caller call out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (Computed.lime_direct_call_iff g.resolves).mp step⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp step⟩
  | framed phase =>
    obtain ⟨out, move, eq⟩ := (Framed.lime_step_iff g.body ready).mp step
    exact ⟨.framed out, framed move, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs.Lime1
