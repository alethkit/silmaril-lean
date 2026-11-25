module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Code
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Transport
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)

theorem sound {H : Type} {s : Store H} {caller : Frame} {call : Invocation}
    {a b : State call} (g : V1Guard s caller call) (edge : Edge call a b) :
    Step CallFrame.v1NoHost (v1Config s caller call a) (v1Config s caller call b) := by
  cases invert edge with
  | framed move => exact Framed.v1_sound g.body move
  | ground rule =>
    cases rule with
    | resolve =>
      simpa only [v1Config, v1Code, render, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ g.resolves) call.args []
    | enter =>
      have count : call.args.length = call.target.declaration.type.params.length := by
        simpa [Declaration.type] using congrArg List.length g.typed.args
      have step := Step.invokeWasm (host := CallFrame.v1NoHost) s caller _ _ _ _ call.args g.allocated count g.scalarResult
      rw [v1_expression] at step
      exact step

theorem readback {H : Type} {s : Store H} {caller : Frame} {call : Invocation}
    {a : State call} {dst : Config H} (g : V1Guard s caller call) (ready : Admitted a)
    (step : Step CallFrame.v1NoHost (v1Config s caller call a) dst) :
    ∃ out, Edge call a out ∧ dst = v1Config s caller call out := by
  have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.config_toLime_injective H (eq.trans (v1_to_lime s caller call out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs.V1
