module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Transport
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Value)
open Computed (v1Syntax)
open StraightLine

private abbrev emit (ctx : Context) := Sequence.emit (site := ctx.sequence) v1Syntax

private theorem attach_code (ctx : Context) (site : Site) (q : DirectSequence.State site) :
    v1Code ctx site (attach ctx q) =
      values ctx.saved ++ DirectSequence.v1Code site q ++ ctx.continuation.map (emit ctx) := by
  cases q with
  | done out =>
    cases out with
    | values =>
      simp only [attach, v1Code, render, DirectSequence.v1Code, DirectSequence.render, Nested.resultCode,
        Sequence.v1Code, Sequence.render,
        values_append]
    | trap =>
      simp only [attach, v1Code, render, DirectSequence.v1Code, DirectSequence.render, Nested.resultCode,
        Sequence.v1Code, Sequence.render,
        List.append_assoc, List.singleton_append]
  | _ => rfl

theorem sound {H : Type} {s : Store H} {ctx : Context} {p : Program} {a b : State ctx p.site}
    (g : V1Guard s ctx p) (edge : Edge ctx p a b) :
    Step CallFrame.v1NoHost (v1Config s ctx p.site a) (v1Config s ctx p.site b) := by
  cases invert edge with
  | invoke _ move =>
    have step := DirectSequence.v1_sound g.invocation move
    simp only [v1Config, attach_code]
    simpa only [v1Config, v1Code, render, DirectSequence.v1Config, List.append_assoc] using
      Step.context step ctx.saved (ctx.continuation.map (emit ctx))
  | resume move => exact Sequence.v1_sound g.continuation move

theorem readback {H : Type} {s : Store H} {ctx : Context} {p : Program} {a : State ctx p.site}
    {dst : Config H} (g : V1Guard s ctx p) (ready : Admitted a)
    (step : Step CallFrame.v1NoHost (v1Config s ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = v1Config s ctx p.site out := by
  have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback ⟨DirectSequence.guard_to_lime g.invocation, Sequence.guard_to_lime g.continuation⟩ ready mapped
  exact ⟨out, edge, CallContinuation.config_toLime_injective H (eq.trans (v1_to_lime s ctx p.site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.V1
