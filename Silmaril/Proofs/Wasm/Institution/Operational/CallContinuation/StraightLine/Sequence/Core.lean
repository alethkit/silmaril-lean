module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Rules
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)
open OuterCall (coreValues)
open OuterCall.Computed

private theorem attach_code {site : Site} (i : site.TargetId) (rest : List (Op site)) (q : CallFrame.State) :
    coreCode site (attach i rest q) =
      CallFrame.coreCode (site.target i).address (site.target i).callee q ++ rest.map (emit coreSyntax) := by
  cases q with
  | trapped => simp only [attach, coreCode, render, CallFrame.coreCode, List.append_assoc, List.singleton_append]
  | _ => rfl

private theorem resolve_iff {H : Type} {P : Profile} {s : Store H} {site : Site} {i : site.TargetId}
    {saved args : List Value} {rest : List (Op site)} {dst : Config H} (g : CoreGuard s site) :
    Step P noHost (coreConfig s site (.running (saved ++ args) (.call i :: rest))) dst ↔
      dst = coreConfig s site (.active i (.invoke saved args) rest) := by
  have exactly := core_direct_call_iff (s := s) (P := P) (f := site.frame) (dst := dst)
    (stack := saved ++ args) (tail := rest.map (emit coreSyntax)) (g.resolves i) (g.allocated i)
  simp only [coreConfig, coreCode, render, CallFrame.coreCode, List.append_assoc, List.cons_append, List.nil_append]
  exact exactly

theorem sound {H : Type} {P : Profile} {s : Store H} {site : Site} {a b : State site}
    (g : CoreGuard s site) (edge : Edge site a b) :
    Step P noHost (coreConfig s site a) (coreConfig s site b) := by
  cases invert edge with
  | @call i _ _ rest _ move =>
    have native := CallFrame.core_sound (P := P) (caller := site.frame) (g.allocated i) move
    simp only [coreConfig, attach_code]
    exact Sim.Step.append_right native (rest.map (emit coreSyntax))
  | ground rule =>
    cases rule with
    | resolve => exact (resolve_iff g).mpr rfl
    | discard cut => exact (Prefix.core_discard_iff (f := site.frame) (emit (site := site) coreSyntax)).mpr ⟨_, _, cut, rfl⟩
    | @numeric stack op rest out move =>
      have native := Prefix.core_step_iff (s := s) (P := P) (f := site.frame)
        (tail := rest.map (emit coreSyntax)) |>.mpr ⟨out, move, rfl⟩
      cases out <;> exact native

theorem readback {H : Type} {P : Profile} {s : Store H} {site : Site} {a : State site}
    {dst : Config H} (g : CoreGuard s site) (ready : Admitted site a) (h : Step P noHost (coreConfig s site a) dst) :
    ∃ out, Edge site a out ∧ dst = coreConfig s site out := by
  cases a with
  | active i phase rest =>
    obtain ⟨mid, step, eq⟩ := CallContinuation.core_active_strip (caller := site.frame) (g.allocated i) ready.1 h
    obtain ⟨out, move, rfl⟩ := (CallFrame.core_step_iff (g.allocated i) ready.2.1).mp step
    exact ⟨attach i rest out, call ready.1 move, eq.trans (by rw [coreConfig, attach_code]; rfl)⟩
  | trapped stack rest =>
    obtain ⟨kept, remaining, cut, eq⟩ :=
      (Prefix.core_discard_iff (f := site.frame) (emit (site := site) coreSyntax)).mp h
    exact ⟨.trapped kept remaining, fact (.discard cut), eq⟩
  | running stack rest =>
    cases rest with
    | nil =>
      have step : Step P noHost ⟨s, site.frame.toCore, coreValues stack⟩ dst := by
        simpa only [coreConfig, coreCode, render, List.map_nil, List.append_nil] using h
      exact (Step.not_vals step).elim
    | cons op rest =>
      cases op with
      | numeric op =>
        obtain ⟨out, move, eq⟩ := (Prefix.core_step_iff (f := site.frame) (op := op)
          (tail := rest.map (emit coreSyntax))).mp h
        exact ⟨afterOp rest out, fact (.numeric move), eq.trans (by cases out <;> rfl)⟩
      | call i =>
        obtain ⟨saved, args, rfl, count⟩ := split ready
        exact ⟨_, fact (.resolve i saved args rest count), (resolve_iff g).mp h⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs.Core
