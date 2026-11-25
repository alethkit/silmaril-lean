module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
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

private abbrev emit := Computed.Prefix.emit coreSyntax

private theorem attach_code (ctx : Context) (site : Site) (q : DirectSequence.State site) :
    coreCode ctx site (attach ctx q) =
      coreValues ctx.saved ++ DirectSequence.coreCode site q ++ ctx.continuation.map emit := by
  cases q with
  | done out =>
    cases out with
    | values =>
      simp only [attach, coreCode, render, DirectSequence.coreCode, DirectSequence.render, Nested.resultCode,
        coreValues, List.map_append, vals_append]
    | trap =>
      simp only [attach, coreCode, render, DirectSequence.coreCode, DirectSequence.render, Nested.resultCode,
        List.append_assoc, List.singleton_append]
  | _ => rfl

theorem sound {H : Type} {P : Profile} {s : Store H} {ctx : Context} {p : Program} {a b : State p.site}
    (g : DirectSequence.CoreGuard s ctx.frame p) (edge : Edge ctx p a b) :
    Step P noHost (coreConfig s ctx p.site a) (coreConfig s ctx p.site b) := by
  cases invert edge with
  | invoke _ move =>
    have step := DirectSequence.core_sound (P := P) g move
    simp only [coreConfig, attach_code]
    simpa only [coreConfig, coreCode, render, DirectSequence.coreConfig, List.append_assoc] using
      Sim.Step.vals_left (Sim.Step.append_right step (ctx.continuation.map emit)) (ctx.saved.map Value.toCore)
  | ground rule =>
    cases rule with
    | @resume stack op rest out move =>
      have step := Computed.Prefix.core_step_iff (s := s) (P := P) (f := ctx.frame)
        (tail := rest.map emit) |>.mpr ⟨out, move, rfl⟩
      cases out <;> exact step
    | discard cut =>
      exact (Computed.Prefix.core_discard_iff (s := s) (P := P) (f := ctx.frame) emit).mpr ⟨_, _, cut, rfl⟩

private theorem active_strip {H : Type} {P : Profile} {s : Store H} {ctx : Context} {p : Program}
    {a : DirectSequence.State p.site} {dst : Config H} (g : DirectSequence.CoreGuard s ctx.frame p)
    (live : Live a) (step : Step P noHost (coreConfig s ctx p.site (.active a)) dst) :
    ∃ mid, Step P noHost (DirectSequence.coreConfig s ctx.frame p.site a) mid ∧
      dst = ⟨mid.store, mid.frame, coreValues ctx.saved ++ mid.code ++ ctx.continuation.map emit⟩ := by
  have stripFrame {n : Nat} {inner : Frame} {body : List Admin}
      (code : DirectSequence.coreCode p.site a = [.frame n inner body]) :
      ∃ mid, Step P noHost (DirectSequence.coreConfig s ctx.frame p.site a) mid ∧
        dst = ⟨mid.store, mid.frame, coreValues ctx.saved ++ mid.code ++ ctx.continuation.map emit⟩ := by
    change Step P noHost
      ⟨s, ctx.frame.toCore, coreValues ctx.saved ++ DirectSequence.coreCode p.site a ++ ctx.continuation.map emit⟩ dst at step
    rw [code, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, eq⟩ := Step.ctx_in_seq (vs := ctx.saved.map Value.toCore) (X := .frame n inner body) (by trivial) step
    refine ⟨mid, ?_, ?_⟩
    · simpa only [DirectSequence.coreConfig, code] using move
    · simpa only [List.append_assoc] using eq
  cases a with
  | call =>
    have focused : Step P noHost
        ⟨s, ctx.frame.toCore, coreValues (ctx.saved ++ p.site.args) ++ .plain (.call p.site.index) ::
          ctx.continuation.map emit⟩ dst := by
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
          .ref (.func p.site.address.value) :: .callRefType p.site.type.toDefType :: ctx.continuation.map emit⟩ dst := by
      simpa only [coreConfig, coreCode, render, DirectSequence.coreCode, DirectSequence.render,
        coreValues, List.map_append, vals_append, List.append_assoc, List.cons_append, List.nil_append] using step
    have enter := (Computed.Sequence.wasm_entry_context_iff (P := P) (caller := ctx.frame)
      (saved := ctx.saved) (rest := ctx.continuation.map emit) g.allocated g.typed.args).mp step
    have init := Computed.Sequence.core_frame_forCall p.site.module p.site.args p.site.locals
    change Frame.forCall p.site.module.toCore (p.site.args.map Value.toCore) p.coreFunc.locals = p.site.frame.toCore at init
    rw [init, DirectSequence.core_body_expression] at enter
    refine ⟨_, DirectSequence.core_sound g (DirectSequence.fact .enter), ?_⟩
    simpa only [DirectSequence.coreConfig, DirectSequence.coreCode, DirectSequence.render,
      Site.type, Site.arity, List.append_assoc, List.singleton_append] using enter
  | label _ | exit _ => exact stripFrame rfl
  | done _ => exact live.elim

theorem readback {H : Type} {P : Profile} {s : Store H} {ctx : Context} {p : Program}
    {a : State p.site} {dst : Config H} (g : DirectSequence.CoreGuard s ctx.frame p)
    (ready : Admitted ctx a) (step : Step P noHost (coreConfig s ctx p.site a) dst) :
    ∃ out, Edge ctx p a out ∧ dst = coreConfig s ctx p.site out := by
  cases a with
  | active q =>
    obtain ⟨mid, isolated, eq⟩ := active_strip g ready.1 step
    obtain ⟨out, edge, rfl⟩ := (DirectSequence.core_step_iff g ready.2).mp isolated
    exact ⟨attach ctx out, invoke ready.1 edge, eq.trans (by rw [coreConfig, attach_code]; rfl)⟩
  | resume stack rest =>
    cases rest with
    | nil =>
      have noStep : Step P noHost ⟨s, ctx.frame.toCore, coreValues stack⟩ dst := by
        simpa only [coreConfig, coreCode, render, List.map_nil, List.append_nil] using step
      exact (Step.not_vals noStep).elim
    | cons op rest =>
      obtain ⟨out, move, eq⟩ := (Computed.Prefix.core_step_iff (f := ctx.frame) (op := op)
        (tail := rest.map emit)).mp step
      exact ⟨afterOp rest out, fact (.resume move), eq.trans (by cases out <;> rfl)⟩
  | trapped stack rest =>
    obtain ⟨kept, pending, cut, eq⟩ := (Computed.Prefix.core_discard_iff (f := ctx.frame) emit).mp step
    exact ⟨.trapped kept pending, fact (.discard cut), eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs.Core
