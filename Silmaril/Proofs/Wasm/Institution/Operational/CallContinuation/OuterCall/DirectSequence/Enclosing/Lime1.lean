module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Rules
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open Computed (limeSyntax)
open StraightLine

private abbrev emit (ctx : Context) := Sequence.emit (site := ctx.sequence) limeSyntax

private theorem attach_code (ctx : Context) (site : Site) (q : DirectSequence.State site) :
    limeCode ctx site (attach ctx q) =
      values ctx.saved ++ DirectSequence.limeCode site q ++ ctx.continuation.map (emit ctx) := by
  cases q with
  | done out =>
    cases out with
    | values =>
      simp only [attach, limeCode, render, DirectSequence.limeCode, DirectSequence.render, Nested.resultCode,
        Sequence.limeCode, Sequence.render,
        values_append]
    | trap =>
      simp only [attach, limeCode, render, DirectSequence.limeCode, DirectSequence.render, Nested.resultCode,
        Sequence.limeCode, Sequence.render,
        List.append_assoc, List.singleton_append]
  | _ => rfl

theorem sound {H : Type} {s : Store H} {ctx : Context} {p : Program} {a b : State ctx p.site}
    (g : LimeGuard s ctx p) (edge : Edge ctx p a b) :
    Step CallFrame.limeNoHost (limeConfig s ctx p.site a) (limeConfig s ctx p.site b) := by
  cases invert edge with
  | invoke _ move =>
    have step := DirectSequence.lime_sound g.invocation move
    simp only [limeConfig, attach_code]
    simpa only [limeConfig, limeCode, render, DirectSequence.limeConfig, List.append_assoc] using
      Step.context step ctx.saved (ctx.continuation.map (emit ctx))
  | resume move => exact Sequence.lime_sound g.continuation move

private theorem active_strip {H : Type} {s : Store H} {ctx : Context} {p : Program}
    {a : DirectSequence.State p.site} {dst : Config H} (g : DirectSequence.LimeGuard s ctx.frame p)
    (live : Live a) (step : Step CallFrame.limeNoHost (limeConfig s ctx p.site (.active a)) dst) :
    ∃ mid, Step CallFrame.limeNoHost (DirectSequence.limeConfig s ctx.frame p.site a) mid ∧
      dst = ⟨mid.store, mid.frame, values ctx.saved ++ mid.code ++ ctx.continuation.map (emit ctx)⟩ := by
  have stripFrame {n : Nat} {inner : Frame} {body : List Admin}
      (code : DirectSequence.limeCode p.site a = [.frame n inner body]) :
      ∃ mid, Step CallFrame.limeNoHost (DirectSequence.limeConfig s ctx.frame p.site a) mid ∧
        dst = ⟨mid.store, mid.frame, values ctx.saved ++ mid.code ++ ctx.continuation.map (emit ctx)⟩ := by
    change Step CallFrame.limeNoHost
      ⟨s, ctx.frame, values ctx.saved ++ DirectSequence.limeCode p.site a ++ ctx.continuation.map (emit ctx)⟩ dst at step
    rw [code, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, eq⟩ := CallContinuation.lime_frame_context_inv step
    refine ⟨mid, ?_, ?_⟩
    · simpa only [DirectSequence.limeConfig, code] using move
    · simpa only [List.append_assoc] using eq
  cases a with
  | call =>
    have focused : Step CallFrame.limeNoHost
        ⟨s, ctx.frame, values (ctx.saved ++ p.site.args) ++ .source (.call p.site.index) ::
          ctx.continuation.map (emit ctx)⟩ dst := by
      simpa only [limeConfig, limeCode, render, DirectSequence.limeCode, DirectSequence.render,
        values_append, List.append_assoc, List.singleton_append] using step
    have eq := (Computed.lime_direct_call_iff g.resolves).mp focused
    refine ⟨_, DirectSequence.lime_sound g (DirectSequence.fact .resolve), ?_⟩
    simpa only [DirectSequence.limeConfig, DirectSequence.limeCode, DirectSequence.render,
      values_append, List.append_assoc, List.cons_append, List.nil_append] using eq
  | invoke =>
    have step : Step CallFrame.limeNoHost
        ⟨s, ctx.frame, values (ctx.saved ++ p.site.args) ++ .invoke p.site.address :: ctx.continuation.map (emit ctx)⟩ dst := by
      simpa only [limeConfig, limeCode, render, DirectSequence.limeCode, DirectSequence.render,
        values_append, List.append_assoc, List.cons_append, List.nil_append] using step
    obtain ⟨mid, step, eq⟩ := CallContinuation.lime_invoke_strip_suffix step
    have count : p.site.args.length = p.site.type.params.length := by
      simpa [Site.type] using congrArg List.length g.typed.args
    have enter := (CallFrame.lime_invoke_wasm_prefix_iff (saved := ctx.saved) g.allocated count).mp step
    rw [DirectSequence.lime_body_expression] at enter
    refine ⟨_, DirectSequence.lime_sound g (DirectSequence.fact .enter), ?_⟩
    exact eq.trans (by rw [enter]; rfl)
  | label _ | exit _ => exact stripFrame rfl
  | done _ => exact live.elim

theorem readback {H : Type} {s : Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {dst : Config H} (g : LimeGuard s ctx p)
    (ready : Admitted a) (step : Step CallFrame.limeNoHost (limeConfig s ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = limeConfig s ctx p.site out := by
  cases a with
  | active q =>
    obtain ⟨mid, isolated, eq⟩ := active_strip g.invocation ready.1 step
    obtain ⟨out, edge, rfl⟩ := (DirectSequence.lime_step_iff g.invocation ready.2).mp isolated
    exact ⟨attach ctx out, invoke ready.1 edge, eq.trans (by rw [limeConfig, attach_code]; rfl)⟩
  | continuation q =>
    obtain ⟨out, edge, eq⟩ := (Sequence.lime_step_iff g.continuation ready).mp step
    exact ⟨.continuation out, resume edge, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.Lime1
