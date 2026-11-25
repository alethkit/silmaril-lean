module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)

private theorem lift_body {H : Type} {s s' : Store H} {caller inner inner' : Frame}
    {n : Nat} {a b : List Admin}
    (h : Step CallFrame.v1NoHost ⟨s, inner, a⟩ ⟨s', inner', b⟩) :
    Step CallFrame.v1NoHost ⟨s, caller, [.frame n inner [.label n [] a]]⟩
      ⟨s', caller, [.frame n inner' [.label n [] b]]⟩ :=
  .frame (.label h n []) n caller

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site} {a b : State site}
    (g : V1Guard s caller site) (edge : Edge site a b) :
    Step CallFrame.v1NoHost (v1Config s caller site a) (v1Config s caller site b) := by
  cases invert edge with
  | nest h => exact Nested.v1_sound g.innerAlloc h
  | ground rule =>
    cases rule with
    | resolve => simpa only [v1Config, v1Code, render, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ g.outerLookup) site.args []
    | enter =>
      have count : site.args.length = site.type.params.length := by
        simpa [Site.type] using congrArg List.length g.typed.outerArgs
      have results : site.type.results.length ≤ 1 := by
        cases site.inner.result <;> simp [Site.type]
      exact .invokeWasm s caller _ _ _ _ site.args g.outerAlloc count results
    | readLeft =>
      exact lift_body (Step.context (Step.localGet s site.frame _ _ g.typed.leftLookup) [] _)
    | readRight =>
      exact lift_body (Step.context (Step.localGet s site.frame _ _ g.typed.rightLookup) [.int site.kind site.left] _)
    | compute ok => exact lift_body (Step.context (.pure s site.frame (.intBinary _ _ _ _ _ ok)) [] _)
    | trap err => exact lift_body (Step.context (.pure s site.frame (.intBinaryTrap _ _ _ _ _ err)) [] _)
    | dropCall => exact lift_body (Step.context (.pure s site.frame (.trapTail _ [])) [] [.source .nop])
    | dropCallAndNop => exact lift_body (.pure s site.frame (.trapTail _ [.source .nop]))
    | resolveInner z =>
      exact lift_body (Step.context (Step.call s site.frame _ _ g.innerLookup) [.int site.kind z] [.source .nop])

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site} {a : State site}
    {dst : Config H} (g : V1Guard s caller site) (ready : Admitted site a)
    (h : Step CallFrame.v1NoHost (v1Config s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = v1Config s caller site out := by
  have mapped := h.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.Proofs.config_toLime_injective H
    (eq.trans (v1_to_lime s caller site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs.V1
