module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame Value)

private theorem evaluating_code (site : Site) (stack : List Value) (remaining : List Prefix.Op) :
    v1Code site (evaluating stack remaining) =
      [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
        (values stack ++ (site.pending remaining).map (site.emit v1Syntax))]] := by
  cases remaining with
  | cons => rfl
  | nil =>
    simp only [evaluating, v1Code, render, StraightLine.v1Code, StraightLine.render, StraightLine.v1Body,
      StraightLine.renderBody, Site.innerSite, List.nil_append, Site.pending, List.map_nil, List.map_cons,
      List.map_map, Function.comp_def, Site.emit]

private theorem after_code (site : Site) (rest : List Prefix.Op) (out : Prefix.Outcome) :
    v1Code site (afterArg site rest out) =
      [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
        (Prefix.outcomeCode values .trap ((site.pending rest).map (site.emit v1Syntax)) out)]] := by
  cases out with
  | values => exact evaluating_code _ _ _
  | trap => rfl

private theorem trap_code (site : Site) (stack : List Value) (rest : List Pending) :
    v1Code site (argumentTrap stack rest) = v1Code site (.argumentTrap stack rest) := by
  cases stack <;> cases rest <;> rfl

private theorem body_expression (site : Site) :
    expression site.v1Func.body = site.body v1Syntax := by
  change (site.body v1Source).map Execution.Runtime.AdminInstr.source = _
  simp only [Site.body, List.map_map]
  apply List.map_congr_left
  intro ins _
  cases ins with
  | op op => cases op <;> rfl
  | call => rfl


private theorem lift_body {H : Type} {s : Store H} {outer caller : Frame} {arity : Nat}
    {before after : List Admin} (step : Step CallFrame.v1NoHost ⟨s, outer, before⟩ ⟨s, outer, after⟩) :
    Step CallFrame.v1NoHost ⟨s, caller, [.frame arity outer [.label arity [] before]]⟩
      ⟨s, caller, [.frame arity outer [.label arity [] after]]⟩ :=
  .frame (.label step arity []) arity caller

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site} {a b : State}
    (g : V1Guard s caller site) (edge : Edge site a b) :
    Step CallFrame.v1NoHost (v1Config s caller site a) (v1Config s caller site b) := by
  cases invert edge with
  | callInner move => exact StraightLine.v1_sound g.innerGuard move
  | ground rule =>
    cases rule with
    | resolve =>
      simpa only [v1Config, v1Code, render, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ g.outerLookup) site.args []
    | enter =>
      have count : site.args.length = site.type.params.length := by
        simpa [Site.type] using congrArg List.length g.typed.outerArgs
      have results : site.type.results.length ≤ 1 := by
        cases site.result <;> simp [Site.type]
      have move := Step.invokeWasm (host := CallFrame.v1NoHost) s caller _ _ _ _ site.args g.outerAlloc count results
      rw [body_expression] at move
      simp only [v1Config, evaluating_code]
      exact move
    | @evaluate stack op remaining out h =>
      have move := Prefix.v1_step_iff (s := s) (f := site.toSite.frame)
        (tail := (site.pending remaining).map (site.emit v1Syntax)) |>.mpr ⟨out, h, rfl⟩
      simp only [v1Config, after_code]
      exact lift_body move
    | discard cut =>
      have move := Prefix.v1_discard_iff (s := s) (f := site.toSite.frame)
        (site.emit v1Syntax) |>.mpr ⟨_, _, cut, rfl⟩
      simp only [v1Config, trap_code]
      exact lift_body (caller := caller) (arity := site.innerSite.arity) move

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site} {a : State}
    {dst : Config H} (g : V1Guard s caller site) (ready : Admitted site a)
    (h : Step CallFrame.v1NoHost (v1Config s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = v1Config s caller site out := by
  have mapped := h.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.Proofs.config_toLime_injective H
    (eq.trans (v1_to_lime s caller site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs.V1
