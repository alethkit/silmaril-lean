module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)
open StraightLine
open Computed (v1Syntax)
open Computed.Sequence (v1Source)

private theorem body_expression (p : Program) :
    expression p.v1Func.body = Sequence.v1Code p.site.body (.running [] p.code) := by
  change (p.body v1Source).map Execution.Runtime.AdminInstr.source = p.body v1Syntax
  simp only [Program.body, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | numeric op => cases op <;> rfl
  | call => rfl

theorem sound {H : Type} {s : Store H} {caller : Frame} {p : Program} {a b : State p.site}
    (g : V1Guard s caller p) (edge : Edge p a b) :
    Step CallFrame.v1NoHost (v1Config s caller p.site a) (v1Config s caller p.site b) := by
  cases invert edge with
  | body move => exact .frame (.label (Sequence.v1_sound g.body move) _ []) _ caller
  | ground move =>
    cases move with
    | resolve =>
      simpa only [v1Config, v1Code, render, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ g.resolves) p.site.args []
    | enter =>
      have count : p.site.args.length = p.site.type.params.length := by
        simpa [Site.type] using congrArg List.length g.typed.args
      have result : p.site.type.results.length ≤ 1 := by
        cases p.site.result <;> simp [Site.type]
      have step := Step.invokeWasm (host := CallFrame.v1NoHost) s caller _ _ _ _ p.site.args g.allocated count result
      rw [body_expression] at step
      exact step
    | leaveLabel finished =>
      cases finished with
      | values stack =>
        have exit : Step CallFrame.v1NoHost
            ⟨s, caller, [.frame p.site.arity p.site.frame [.label p.site.arity [] (values stack)]]⟩
            (v1Config s caller p.site (.exit (.values stack))) :=
          .frame (.pure s p.site.frame (.labelDone _ [] stack)) _ caller
        simpa only [v1Config, v1Code, render, Sequence.v1Code, Sequence.render, List.map_nil, List.append_nil] using exit
      | trap => exact .frame (.pure s p.site.frame (.labelTrap _ [])) _ caller
    | leaveFrame result arity =>
      cases result with
      | values stack => exact .pure s caller (.frameDone _ _ stack arity)
      | trap => exact .pure s caller (.frameTrap _ _)

theorem readback {H : Type} {s : Store H} {caller : Frame} {p : Program} {a : State p.site}
    {dst : Config H} (g : V1Guard s caller p) (ready : Admitted p.site a)
    (step : Step CallFrame.v1NoHost (v1Config s caller p.site a) dst) :
    ∃ out, Edge p a out ∧ dst = v1Config s caller p.site out := by
  have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.config_toLime_injective H
    (eq.trans (v1_to_lime s caller p.site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs.V1
