module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Rules
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.Core

open Execution.Core
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)
open Execution.Runtime (Value)
open Computed (coreSyntax)
open StraightLine

private abbrev emit (ctx : Context) := Sequence.emit (site := ctx.sequence) coreSyntax

private theorem attach_code (ctx : Context) (site : Site) (q : DirectSequence.State site) :
    coreCode ctx site (attach ctx q) =
      coreValues ctx.saved ++ DirectSequence.coreCode site q ++ ctx.continuation.map (emit ctx) := by
  cases q with
  | done out =>
    cases out with
    | values =>
      simp only [attach, coreCode, render, DirectSequence.coreCode, DirectSequence.render, Nested.resultCode,
        Sequence.coreCode, Sequence.render,
        coreValues, List.map_append, vals_append]
    | trap =>
      simp only [attach, coreCode, render, DirectSequence.coreCode, DirectSequence.render, Nested.resultCode,
        Sequence.coreCode, Sequence.render,
        List.append_assoc, List.singleton_append]
  | _ => rfl

theorem sound {H : Type} {P : Profile} {s : Store H} {ctx : Context} {p : Program} {a b : State ctx p.site}
    (g : CoreGuard s ctx p) (edge : Edge ctx p a b) :
    Step P noHost (coreConfig s ctx p.site a) (coreConfig s ctx p.site b) := by
  cases invert edge with
  | invoke _ move =>
    have step := DirectSequence.core_sound (P := P) g.invocation move
    simp only [coreConfig, attach_code]
    simpa only [coreConfig, coreCode, render, DirectSequence.coreConfig, List.append_assoc] using
      Sim.Step.vals_left (Sim.Step.append_right step (ctx.continuation.map (emit ctx))) (ctx.saved.map Value.toCore)
  | resume move => exact Sequence.core_sound g.continuation move

private theorem active_strip {H : Type} {P : Profile} {s : Store H} {ctx : Context} {p : Program}
    {a : DirectSequence.State p.site} {dst : Config H} (g : DirectSequence.CoreGuard s ctx.frame p)
    (live : Live a) (step : Step P noHost (coreConfig s ctx p.site (.active a)) dst) :
    ∃ mid, Step P noHost (DirectSequence.coreConfig s ctx.frame p.site a) mid ∧
      dst = ⟨mid.store, mid.frame, coreValues ctx.saved ++ mid.code ++ ctx.continuation.map (emit ctx)⟩ := by
  have stripFrame {n : Nat} {inner : Frame} {body : List Admin}
      (code : DirectSequence.coreCode p.site a = [.frame n inner body]) :
      ∃ mid, Step P noHost (DirectSequence.coreConfig s ctx.frame p.site a) mid ∧
        dst = ⟨mid.store, mid.frame, coreValues ctx.saved ++ mid.code ++ ctx.continuation.map (emit ctx)⟩ := by
    change Step P noHost
      ⟨s, ctx.frame.toCore, coreValues ctx.saved ++ DirectSequence.coreCode p.site a ++ ctx.continuation.map (emit ctx)⟩ dst at step
    rw [code, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, eq⟩ := Step.ctx_in_seq (vs := ctx.saved.map Value.toCore) (X := .frame n inner body) (by trivial) step
    refine ⟨mid, ?_, ?_⟩
    · simpa only [DirectSequence.coreConfig, code] using move
    · simpa only [List.append_assoc] using eq
  cases a with
  | call =>
    have focused : Step P noHost
        ⟨s, ctx.frame.toCore, coreValues (ctx.saved ++ p.site.args) ++ .plain (.call p.site.index) ::
          ctx.continuation.map (emit ctx)⟩ dst := by
      simpa only [coreConfig, coreCode, render, DirectSequence.coreCode, DirectSequence.render,
        coreValues, List.map_append, vals_append, List.append_assoc, List.singleton_append] using step
    have eq := (Computed.core_direct_call_iff g.resolves g.allocated).mp focused
    refine ⟨_, DirectSequence.core_sound (P := P) g (DirectSequence.fact .resolve), ?_⟩
    simpa only [DirectSequence.coreConfig, DirectSequence.coreCode, DirectSequence.render,
      Program.coreInstance, coreValues, List.map_append, vals_append, List.append_assoc, List.cons_append,
      List.nil_append] using eq
  | invoke =>
    have step : Step P noHost
        ⟨s, ctx.frame.toCore, coreValues (ctx.saved ++ p.site.args) ++
          .ref (.func p.site.address.value) :: .callRefType p.site.type.toDefType :: ctx.continuation.map (emit ctx)⟩ dst := by
      simpa only [coreConfig, coreCode, render, DirectSequence.coreCode, DirectSequence.render,
        coreValues, List.map_append, vals_append, List.append_assoc, List.cons_append, List.nil_append] using step
    have enter := (Computed.Sequence.wasm_entry_context_iff (P := P) (caller := ctx.frame)
      (saved := ctx.saved) (rest := ctx.continuation.map (emit ctx)) g.allocated g.typed.args).mp step
    have init := Computed.Sequence.core_frame_forCall p.site.module p.site.args p.site.locals
    change Frame.forCall p.site.module.toCore (p.site.args.map Value.toCore) p.coreFunc.locals = p.site.frame.toCore at init
    rw [init, DirectSequence.core_body_expression] at enter
    refine ⟨_, DirectSequence.core_sound g (DirectSequence.fact .enter), ?_⟩
    simpa only [DirectSequence.coreConfig, DirectSequence.coreCode, DirectSequence.render,
      Site.type, Site.arity, List.append_assoc, List.singleton_append] using enter
  | label _ | exit _ => exact stripFrame rfl
  | done _ => exact live.elim

theorem readback {H : Type} {P : Profile} {s : Store H} {ctx : Context} {p : Program}
    {a : State ctx p.site} {dst : Config H} (g : CoreGuard s ctx p)
    (ready : Admitted a) (step : Step P noHost (coreConfig s ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = coreConfig s ctx p.site out := by
  cases a with
  | active q =>
    obtain ⟨mid, isolated, eq⟩ := active_strip g.invocation ready.1 step
    obtain ⟨out, edge, rfl⟩ := (DirectSequence.core_step_iff g.invocation ready.2).mp isolated
    exact ⟨attach ctx out, invoke ready.1 edge, eq.trans (by rw [coreConfig, attach_code]; rfl)⟩
  | continuation q =>
    obtain ⟨out, edge, eq⟩ := (Sequence.core_step_iff g.continuation ready).mp step
    exact ⟨.continuation out, resume edge, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.Core
