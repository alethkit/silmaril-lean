module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Transport
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)
open StraightLine

theorem sound {H : Type} {s : Store H} {caller : Frame}
    {ctx : Context} {p : Program} {a b : State ctx p.site} (g : Enclosing.V1Guard s ctx p)
    (edge : Edge ctx p a b) : Step CallFrame.v1NoHost (v1Config s caller ctx p.site a) (v1Config s caller ctx p.site b) := by
  cases invert edge with
  | body move => exact .frame (.label (Enclosing.v1_sound g move) _ []) _ caller
  | ground rule =>
    cases rule with
    | leaveLabel finished =>
      cases finished with
      | values stack =>
        have leave : Step CallFrame.v1NoHost
            ⟨s, caller, [.frame ctx.sequence.results.length ctx.frame
              [.label ctx.sequence.results.length [] (values stack)]]⟩
            (v1Config s caller ctx p.site (.exit (.values stack))) :=
          .frame (.pure s ctx.frame (.labelDone _ [] stack)) _ caller
        simpa only [v1Config, v1Code, render, Enclosing.v1Code, Enclosing.render, Sequence.v1Code,
          Sequence.render, List.map_nil, List.append_nil] using leave
      | trap => exact .frame (.pure s ctx.frame (.labelTrap _ [])) _ caller
    | leaveFrame result arity =>
      cases result with
      | values stack => exact .pure s caller (.frameDone _ _ stack arity)
      | trap => exact .pure s caller (.frameTrap _ _)

theorem readback {H : Type} {s : Store H} {caller : Frame} {ctx : Context} {p : Program}
    {a : State ctx p.site} {dst : Config H} (g : Enclosing.V1Guard s ctx p) (ready : Admitted a)
    (step : Step CallFrame.v1NoHost (v1Config s caller ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = v1Config s caller ctx p.site out := by
  have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (Enclosing.guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.config_toLime_injective H (eq.trans (v1_to_lime s caller ctx p.site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs.V1
