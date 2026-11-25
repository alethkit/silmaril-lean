module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Rules
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame)
open StraightLine

private theorem invocation_stays {ctx : Context} {site : Site} {n : Nat}
    {q : DirectSequence.State site} {tail out : List Admin} (live : Enclosing.Live q)
    (step : PureStep ctx.frame.module.types [.label n [] (values ctx.saved ++ DirectSequence.limeCode site q ++ tail)] out) : False := by
  have frame {k : Nat} {inside : Frame} {body : List Admin}
      (code : DirectSequence.limeCode site q = [.frame k inside body]) : False := by
    have h := step
    rw [code, List.append_assoc, List.singleton_append] at h
    exact Computed.lime_label_stays (stack := ctx.saved) (head := .frame k inside body)
      rfl (by simp) (by simp) (by simp) h
  cases q with
  | label _ | exit _ => exact frame rfl
  | call =>
    have h : PureStep ctx.frame.module.types [.label n [] (values (ctx.saved ++ site.args) ++ .source (.call site.index) :: tail)] out := by
      simpa only [DirectSequence.limeCode, DirectSequence.render, values_append, List.append_assoc,
        List.singleton_append] using step
    exact Computed.lime_label_stays (stack := ctx.saved ++ site.args) (head := .source (.call site.index)) rfl (by simp) (by simp) (by simp) h
  | invoke =>
    have h : PureStep ctx.frame.module.types [.label n [] (values (ctx.saved ++ site.args) ++ .invoke site.address :: tail)] out := by
      simpa only [DirectSequence.limeCode, DirectSequence.render, values_append, List.append_assoc,
        List.cons_append, List.nil_append] using step
    exact Computed.lime_label_stays (stack := ctx.saved ++ site.args) (head := .invoke site.address) rfl (by simp) (by simp) (by simp) h
  | done _ => exact live.elim

theorem sound {H : Type} {s : Store H} {caller : Frame}
    {ctx : Context} {p : Program} {a b : State ctx p.site} (g : Enclosing.LimeGuard s ctx p)
    (edge : Edge ctx p a b) : Step CallFrame.limeNoHost (limeConfig s caller ctx p.site a) (limeConfig s caller ctx p.site b) := by
  cases invert edge with
  | body move => exact .frame (.label (Enclosing.lime_sound g move) _ []) _ caller
  | ground rule =>
    cases rule with
    | leaveLabel finished =>
      cases finished with
      | values stack =>
        have leave : Step CallFrame.limeNoHost
            ⟨s, caller, [.frame ctx.sequence.results.length ctx.frame
              [.label ctx.sequence.results.length [] (values stack)]]⟩
            (limeConfig s caller ctx p.site (.exit (.values stack))) :=
          .frame (.pure s ctx.frame (.labelDone _ [] stack)) _ caller
        simpa only [limeConfig, limeCode, render, Enclosing.limeCode, Enclosing.render, Sequence.limeCode,
          Sequence.render, List.map_nil, List.append_nil] using leave
      | trap => exact .frame (.pure s ctx.frame (.labelTrap _ [])) _ caller
    | leaveFrame result arity =>
      cases result with
      | values stack => exact .pure s caller (.frameDone _ _ stack arity)
      | trap => exact .pure s caller (.frameTrap _ _)

theorem readback {H : Type} {s : Store H} {caller : Frame}
    {ctx : Context} {p : Program} {a : State ctx p.site} {dst : Config H} (g : Enclosing.LimeGuard s ctx p)
    (ready : Admitted a) (step : Step CallFrame.limeNoHost (limeConfig s caller ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = limeConfig s caller ctx p.site out := by
  cases a with
  | label q =>
    rcases Computed.lime_body_step_cases step with ⟨mid, bodyStep, eq⟩ | ⟨_, pop, eq⟩
    · obtain ⟨out, move, rfl⟩ := (Enclosing.lime_step_iff g ready).mp bodyStep
      exact ⟨.label out, underLabel move, eq⟩
    · cases q with
      | active phase => exact (invocation_stays ready.1 pop).elim
      | continuation phase =>
        obtain ⟨result, finished, rfl⟩ := Sequence.lime_label_result ready pop
        exact ⟨.exit result, fact (.leaveLabel finished), eq⟩
  | exit r =>
    exact ⟨.done r, fact (.leaveFrame r (Sequence.result_arity ready)), Nested.lime_frame_result step⟩
  | done r => exact (Nested.lime_result_stuck step).elim

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs.Lime1
