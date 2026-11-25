module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (Frame Value)
open OuterCall.Computed

private abbrev emit := Prefix.emit v1Syntax

private theorem lift_body {H : Type} {s : Store H} {caller outer : Frame} {n : Nat}
    {a b : List Admin} (h : Step CallFrame.v1NoHost ⟨s, outer, a⟩ ⟨s, outer, b⟩) :
    Step CallFrame.v1NoHost ⟨s, caller, [.frame n outer [.label n [] a]]⟩
      ⟨s, caller, [.frame n outer [.label n [] b]]⟩ :=
  .frame (.label h n []) n caller

private theorem resumed_code (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    v1Code site (resumed stack rest) =
      [.frame site.arity site.outer [.label site.arity [] (values stack ++ rest.map emit)]] := by
  cases rest with
  | nil => simp only [resumed, v1Code, render, Nested.v1Code, Nested.render, CallContinuation.v1Code,
      CallContinuation.render, List.map_nil, List.append_nil]
  | cons => rfl

private theorem trapped_code (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    v1Code site (trapped stack rest) =
      [.frame site.arity site.outer [.label site.arity [] (values stack ++ .trap :: rest.map emit)]] := by
  cases stack <;> cases rest <;> rfl

private theorem attach_code (site : Site) (a : CallFrame.State) :
    v1Code site (attach site a) = [.frame site.arity site.outer [.label site.arity []
      (CallFrame.v1Code site.address site.callee a ++ site.continuation.map emit)]] := by
  cases a with
  | returned => rw [attach, resumed_code]; rfl
  | trapped =>
    rw [attach, trapped_code]
    simp only [CallFrame.v1Code, CallFrame.legacyCode, values, List.append_assoc, List.singleton_append]
  | _ => rfl

private theorem after_code (site : Site) (rest : List Prefix.Op) (ans : Prefix.Outcome) :
    v1Code site (afterOp rest ans) = [.frame site.arity site.outer [.label site.arity []
      (Prefix.outcomeCode values .trap (rest.map emit) ans)]] := by
  cases ans with
  | values => exact resumed_code _ _ _
  | trap => exact trapped_code _ _ _

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site}
    {a b : State} (g : V1Guard s site) (edge : Edge site a b) :
    Step CallFrame.v1NoHost (v1Config s caller site a) (v1Config s caller site b) := by
  cases invert edge with
  | @call a b _ inner =>
    have step := CallFrame.v1_sound (caller := site.outer) g.allocated inner
    simp only [v1Config, attach_code]
    have lifted : Step CallFrame.v1NoHost
        ⟨s, site.outer, CallFrame.v1Code site.address site.callee a ++ site.continuation.map emit⟩
        ⟨s, site.outer, CallFrame.v1Code site.address site.callee b ++ site.continuation.map emit⟩ := by
      simpa only [values, List.map_nil, List.nil_append] using Step.context step [] (site.continuation.map emit)
    exact lift_body lifted
  | ground rule =>
    cases rule with
    | resolve saved args =>
      have step := Step.context (Step.call (host := CallFrame.v1NoHost) s site.outer _ _ g.lookup)
        (saved ++ args) (site.continuation.map emit)
      have lifted : Step CallFrame.v1NoHost ⟨s, site.outer, v1Body site (.call saved args)⟩
          ⟨s, site.outer, v1Body site (.active (.invoke saved args))⟩ := by
        change Step CallFrame.v1NoHost
          ⟨s, site.outer, values (saved ++ args) ++ .source (.call site.index) :: site.continuation.map emit⟩
          ⟨s, site.outer, values (saved ++ args) ++ [.invoke site.address] ++ site.continuation.map emit⟩
        simpa only [List.append_assoc, List.singleton_append] using step
      exact lift_body lifted
    | @resume stack op rest ans h =>
      have move := Prefix.v1_step_iff (s := s) (f := site.outer) (tail := rest.map emit) |>.mpr ⟨ans, h, rfl⟩
      simp only [v1Config, after_code]
      exact lift_body move
    | discard h =>
      have move := Prefix.v1_discard_iff (s := s) (f := site.outer) emit |>.mpr ⟨_, _, h, rfl⟩
      simp only [v1Config, trapped_code]
      exact lift_body move
    | boundary h => exact Nested.v1_sound g.allocated (Nested.fact h)

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site} {a : State} {dst : Config H}
    (g : V1Guard s site) (ready : Admitted site a)
    (h : Step CallFrame.v1NoHost (v1Config s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = v1Config s caller site out := by
  have mapped := h.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ proof => proof)
  rw [v1_to_lime] at mapped
  obtain ⟨out, edge, eq⟩ := Lime1.readback (guard_to_lime g) ready mapped
  exact ⟨out, edge, CallContinuation.Proofs.config_toLime_injective H
    (eq.trans (v1_to_lime s caller site out).symm)⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs.V1
