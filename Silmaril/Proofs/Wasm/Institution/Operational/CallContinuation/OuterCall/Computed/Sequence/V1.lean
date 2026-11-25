module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame Value)

private theorem lift_body {H : Type} {s s' : Store H} {caller inner inner' : Frame}
    {n : Nat} {a b : List Admin}
    (h : Step CallFrame.v1NoHost ⟨s, inner, a⟩ ⟨s', inner', b⟩) :
    Step CallFrame.v1NoHost ⟨s, caller, [.frame n inner [.label n [] a]]⟩
      ⟨s', caller, [.frame n inner' [.label n [] b]]⟩ :=
  .frame (.label h n []) n caller

private theorem body_expression (site : Site) :
    expression site.v1Func.body = site.body v1Syntax := by
  change (site.body v1Source).map Execution.Runtime.AdminInstr.source = _
  simp only [Site.body, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | arg op => cases op <;> rfl
  | call | nop => rfl

private theorem eval {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {ans : Prefix.Outcome}
    (h : Prefix.Reduce site.frame.locals stack op ans) :
    Step CallFrame.v1NoHost (v1Config s caller site (.args stack (op :: rest))) (v1Config s caller site (afterOp rest ans)) := by
  have step := Prefix.v1_step_iff (s := s) (f := site.frame)
    (tail := (pending rest).map (site.pendingOp v1Syntax)) |>.mpr ⟨ans, h, rfl⟩
  cases ans <;> exact lift_body step

private theorem inner_start_code (site : Site) (stack : List Value) :
    v1Code site (.nested (innerStart stack)) = [.frame site.arity site.frame
      [.label site.arity [] (values stack ++ [.invoke site.innerAddr, .source .nop])]] := by
  simp only [v1Code, render, innerStart, Nested.v1Code, Nested.render, CallContinuation.v1Code,
    CallContinuation.render, CallFrame.v1Code, CallFrame.legacyCode, values, List.nil_append,
    List.append_assoc, List.cons_append]

private theorem render_trap (site : Site) (stack : List Value) (rest : List Pending) :
    v1Code site (trapState stack rest) = v1Code site (.trap stack rest) := by
  cases stack <;> cases rest <;> rfl

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site} {a b : State}
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
      have step := Step.invokeWasm (host := CallFrame.v1NoHost) s caller _ _ _ _ site.args g.outerAlloc count results
      rw [body_expression] at step
      exact step
    | arg h => exact eval h
    | trap h => exact eval h
    | resolveInner stack =>
      simp only [v1Config, inner_start_code]
      have step : Step CallFrame.v1NoHost
          ⟨s, site.frame, values stack ++ [.source (.call site.innerIndex), .source .nop]⟩
          ⟨s, site.frame, values stack ++ [.invoke site.innerAddr, .source .nop]⟩ := by
        simpa only [List.append_assoc, List.singleton_append] using
          Step.context (Step.call (host := CallFrame.v1NoHost) s site.frame _ _ g.innerLookup) stack [.source .nop]
      exact lift_body step
    | discard cut =>
      have step := Prefix.v1_discard_iff (s := s) (f := site.frame)
        (site.pendingOp v1Syntax) |>.mpr ⟨_, _, cut, rfl⟩
      simp only [v1Config, render_trap]
      exact lift_body (caller := caller) (n := site.arity) step

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site} {a : State}
    {dst : Config H} (g : V1Guard s caller site) (ready : Admitted site a)
    (h : Step CallFrame.v1NoHost (v1Config s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = v1Config s caller site out := by
  have mapped := h.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.Proofs.config_toLime_injective H
    (eq.trans (v1_to_lime s caller site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs.V1
