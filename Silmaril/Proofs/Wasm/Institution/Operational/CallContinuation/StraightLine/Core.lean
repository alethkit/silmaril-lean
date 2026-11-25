module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Core

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)
open OuterCall (coreValues)
open OuterCall.Computed
open OuterCall.Computed.Proofs.Core (label_stays read_body lift_body call_iff)

private abbrev emit := Prefix.emit coreSyntax

private theorem resumed_code (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    coreCode site (resumed stack rest) =
      [.frame site.arity site.outer.toCore [.label site.arity [] (coreValues stack ++ rest.map emit)]] := by
  cases rest with
  | nil => simp only [resumed, coreCode, render, Nested.coreCode, Nested.render, CallContinuation.coreCode,
      CallContinuation.render, List.map_nil, List.append_nil]
  | cons => rfl

private theorem trapped_code (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    coreCode site (trapped stack rest) =
      [.frame site.arity site.outer.toCore [.label site.arity [] (coreValues stack ++ .trap :: rest.map emit)]] := by
  cases stack <;> cases rest <;> rfl

private theorem attach_code (site : Site) (a : CallFrame.State) :
    coreCode site (attach site a) = [.frame site.arity site.outer.toCore [.label site.arity []
      (CallFrame.coreCode site.address site.callee a ++ site.continuation.map emit)]] := by
  cases a with
  | returned => rw [attach, resumed_code]; rfl
  | trapped => rw [attach, trapped_code]; simp only [CallFrame.coreCode, List.append_assoc, List.singleton_append]
  | _ => rfl

private theorem after_code (site : Site) (rest : List Prefix.Op) (ans : Prefix.Outcome) :
    coreCode site (afterOp rest ans) = [.frame site.arity site.outer.toCore [.label site.arity []
      (Prefix.outcomeCode coreValues .trap (rest.map emit) ans)]] := by
  cases ans with
  | values => exact resumed_code _ _ _
  | trap => exact trapped_code _ _ _

private theorem active_stays {site : Site} {q : CallFrame.State} (live : Active q) {out : List Admin}
    (h : LabelExit site.arity [] (coreBody site (.active q)) out) : False := by
  cases q with
  | invoke saved args =>
    let rf := Val.ref (.func site.address.value)
    let instr := Admin.callRefType site.callee.type.toDefType
    have code : coreBody site (.active (.invoke saved args)) =
        vals ((saved ++ args).map Value.toCore ++ [rf]) ++ instr :: site.continuation.map emit := by
      simp only [coreBody, renderBody, CallFrame.coreCode, vals_append, List.append_assoc, List.cons_append,
        List.nil_append]
      rfl
    rw [code] at h
    exact label_stays (head := instr) rfl (by simp [instr]) (by simp [instr])
      (by simp [instr, Admin.IsReturnCallRef]) (by simp [instr]) (by simp [instr]) h
  | label saved ls body =>
    let op := Admin.frame site.callee.arity (site.callee.frame ls).toCore
      [.label site.callee.arity [] (CallFrame.coreBody body)]
    change LabelExit site.arity [] (coreValues saved ++ [op] ++ site.continuation.map emit) out at h
    rw [List.append_assoc, List.singleton_append] at h
    exact label_stays rfl (by simp [op]) (by simp [op]) (by simp [op, Admin.IsReturnCallRef])
      (by simp [op]) (by simp [op]) h
  | exit saved ls ready =>
    let op := Admin.frame site.callee.arity (site.callee.frame ls).toCore (CallFrame.coreExit ready)
    change LabelExit site.arity [] (coreValues saved ++ [op] ++ site.continuation.map emit) out at h
    rw [List.append_assoc, List.singleton_append] at h
    exact label_stays rfl (by simp [op]) (by simp [op]) (by simp [op, Admin.IsReturnCallRef])
      (by simp [op]) (by simp [op]) h
  | returned | trapped => exact live.elim

private theorem resolve_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {saved args : List Value} {dst : Config H} (g : CoreGuard s site) :
    Step P noHost (coreConfig s caller site (.call saved args)) dst ↔
      dst = coreConfig s caller site (.active (.invoke saved args)) := by
  have equal : CallFrame.coreCode site.address site.callee (.invoke saved args) ++ site.continuation.map emit =
      coreValues (saved ++ args) ++ .ref (.func site.address.value) ::
        .callRefType site.callee.type.toDefType :: site.continuation.map emit := by
    simp only [CallFrame.coreCode, List.append_assoc, List.cons_append, List.nil_append]
  constructor
  · intro h
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := (saved ++ args).map Value.toCore) (head := .plain (.call site.index))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)) h
    have read := (call_iff g.lookup g.allocated).mp move
    exact eq.trans (by rw [read]; simp only [coreConfig, coreCode, render, coreBody, renderBody, equal]; rfl)
  · rintro rfl
    simp only [coreConfig, coreCode, render, coreBody, renderBody, equal]
    exact lift_body ((call_iff g.lookup g.allocated).mpr rfl)

private theorem resume_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step P noHost (coreConfig s caller site (.resume stack (op :: rest))) dst ↔
      ∃ out, Prefix.Reduce site.outer.locals stack op out ∧ dst = coreConfig s caller site (afterOp rest out) := by
  have stays {out} : LabelExit site.arity [] (coreValues stack ++ emit op :: rest.map emit) out → False := by
    cases op <;> exact label_stays rfl (by simp [emit, Prefix.emit, coreSyntax]) (by simp [emit, Prefix.emit, coreSyntax])
      (by simp [emit, Prefix.emit, coreSyntax, Admin.IsReturnCallRef]) (by simp [emit, Prefix.emit, coreSyntax])
      (by simp [emit, Prefix.emit, coreSyntax])
  constructor
  · intro h
    obtain ⟨mid, move, eq⟩ := read_body stays h
    obtain ⟨out, reduce, rfl⟩ := Prefix.core_step_iff.mp move
    exact ⟨out, reduce, eq.trans (by rw [coreConfig, after_code])⟩
  · rintro ⟨out, reduce, rfl⟩
    have step := Prefix.core_step_iff (s := s) (P := P) (f := site.outer)
      (tail := rest.map emit) |>.mpr ⟨out, reduce, rfl⟩
    simp only [coreConfig, after_code]
    exact lift_body step

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame} {site : Site}
    {a b : State} (g : CoreGuard s site) (edge : Edge site a b) :
    Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) := by
  cases invert edge with
  | call _ inner =>
    have step := CallFrame.core_sound (P := P) (caller := site.outer) g.allocated inner
    simp only [coreConfig, attach_code]
    exact lift_body (Sim.Step.append_right step (site.continuation.map emit))
  | ground rule =>
    cases rule with
    | resolve => exact (resolve_iff g).mpr rfl
    | resume h => exact resume_iff.mpr ⟨_, h, rfl⟩
    | discard h =>
      have move := Prefix.core_discard_iff (s := s) (P := P) (f := site.outer) emit |>.mpr ⟨_, _, h, rfl⟩
      simp only [coreConfig, trapped_code]
      exact lift_body move
    | boundary h => exact Nested.core_sound g.allocated (Nested.fact h)

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame} {site : Site}
    {a : State} {dst : Config H} (g : CoreGuard s site) (ready : Admitted site a)
    (step : Step P noHost (coreConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = coreConfig s caller site out := by
  cases a with
  | call saved args => exact ⟨_, fact (.resolve saved args), (resolve_iff g).mp step⟩
  | active q =>
    obtain ⟨mid, inner, eq⟩ := read_body (active_stays ready.1) step
    obtain ⟨mid', move, rfl⟩ := CallContinuation.Proofs.active_strip g.allocated ready.1 inner
    obtain ⟨out, edge, rfl⟩ := (CallFrame.core_step_iff g.allocated ready.2.1).mp move
    exact ⟨attach site out, call ready.1 edge, eq.trans (by rw [coreConfig, attach_code]; rfl)⟩
  | resume stack rest =>
    cases rest with
    | nil => exact (ready.1 rfl).elim
    | cons op rest =>
      obtain ⟨out, move, eq⟩ := resume_iff.mp step
      exact ⟨_, fact (.resume move), eq⟩
  | trapped stack rest =>
    have nonempty : stack.map Value.toCore ≠ [] ∨ rest.map emit ≠ [] := by simpa [Admitted] using ready
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := stack.map Value.toCore) (head := .trap) rfl (by simp) (by simp)
        (by simp [Admin.IsReturnCallRef]) (by simp) (fun _ => nonempty)) step
    obtain ⟨kept, rest, cut, rfl⟩ := (Prefix.core_discard_iff (f := site.outer) emit).mp move
    exact ⟨_, fact (.discard cut), eq.trans (by rw [coreConfig, trapped_code])⟩
  | boundary phase =>
    have guard := nested_ready (site := site) ready
    obtain ⟨out, edge, eq⟩ := (Nested.core_step_iff g.allocated guard).mp step
    exact ⟨_, fact (.boundary (boundary_ground ready edge)), eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs.Core
