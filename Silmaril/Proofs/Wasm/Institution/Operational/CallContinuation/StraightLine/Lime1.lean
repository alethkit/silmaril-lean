module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open OuterCall.Computed
open OuterCall.Computed.Proofs.Lime1 (label_stays read_body lift_body call_iff)

private abbrev emit := Prefix.emit limeSyntax

private theorem resumed_code (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    limeCode site (resumed stack rest) =
      [.frame site.arity site.outer [.label site.arity [] (values stack ++ rest.map emit)]] := by
  cases rest with
  | nil => simp only [resumed, limeCode, render, Nested.limeCode, Nested.render, CallContinuation.limeCode,
      CallContinuation.render, List.map_nil, List.append_nil]
  | cons => rfl

private theorem trapped_code (site : Site) (stack : List Value) (rest : List Prefix.Op) :
    limeCode site (trapped stack rest) =
      [.frame site.arity site.outer [.label site.arity [] (values stack ++ .trap :: rest.map emit)]] := by
  cases stack <;> cases rest <;> rfl

private theorem attach_code (site : Site) (a : CallFrame.State) :
    limeCode site (attach site a) = [.frame site.arity site.outer [.label site.arity []
      (CallFrame.limeCode site.address site.callee a ++ site.continuation.map emit)]] := by
  cases a with
  | returned => rw [attach, resumed_code]; rfl
  | trapped => rw [attach, trapped_code]; simp only [CallFrame.limeCode, CallFrame.legacyCode, values, List.append_assoc, List.singleton_append]
  | _ => rfl

private theorem after_code (site : Site) (rest : List Prefix.Op) (ans : Prefix.Outcome) :
    limeCode site (afterOp rest ans) = [.frame site.arity site.outer [.label site.arity []
      (Prefix.outcomeCode values .trap (rest.map emit) ans)]] := by
  cases ans with
  | values => exact resumed_code _ _ _
  | trap => exact trapped_code _ _ _

theorem active_label_stays {addr : Execution.Runtime.FuncAddr} {fn : CallFrame.Callee}
    {types : List Wasm.Lime1.FuncType} {arity : Nat} {q : CallFrame.State} {suffix out : List Admin}
    (live : Active q) (h : PureStep types [.label arity [] (CallFrame.limeCode addr fn q ++ suffix)] out) : False := by
  have preserve {stack : List Value} {op : Admin}
      (nonvalue : asValue? op = none) (notBr : ∀ i, op ≠ .source (.br i))
      (notRet : op ≠ .source .return_) (notTrap : op ≠ .trap)
      (code : CallFrame.limeCode addr fn q ++ suffix = values stack ++ [op] ++ suffix) : False := by
    rw [code, List.append_assoc, List.singleton_append] at h
    exact label_stays nonvalue notBr notRet (fun eq => (notTrap eq).elim) h
  cases q with
  | invoke saved args =>
    exact preserve (stack := saved ++ args) (op := .invoke addr) rfl (by simp) (by simp) (by simp) rfl
  | label saved ls body =>
    exact preserve
      (stack := saved) (op := .frame fn.arity (fn.frame ls) [.label fn.arity [] (CallFrame.legacyBody Locals.limeInstr .return_ .unreachable body)])
      rfl (by simp) (by simp) (by simp) rfl
  | exit saved ls ready =>
    exact preserve
      (stack := saved) (op := .frame fn.arity (fn.frame ls) (CallFrame.legacyExit value .return_ ready))
      rfl (by simp) (by simp) (by simp) rfl
  | returned | trapped => exact live.elim

private theorem resolve_iff {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {saved args : List Value} {dst : Config H} (g : LimeGuard s site) :
    Step CallFrame.limeNoHost (limeConfig s caller site (.call saved args)) dst ↔
      dst = limeConfig s caller site (.active (.invoke saved args)) := by
  have equal : CallFrame.limeCode site.address site.callee (.invoke saved args) ++ site.continuation.map emit =
      values (saved ++ args) ++ .invoke site.address :: site.continuation.map emit := by
    simp only [CallFrame.limeCode, CallFrame.legacyCode, values, List.append_assoc, List.singleton_append]
  constructor
  · intro h
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := saved ++ args) (head := .source (.call site.index)) rfl (by simp) (by simp) (by simp)) h
    have read := (call_iff g.lookup).mp move
    exact eq.trans (by rw [read]; simp only [limeConfig, limeCode, render, limeBody, renderBody, equal])
  · rintro rfl
    simp only [limeConfig, limeCode, render, limeBody, renderBody, equal]
    exact lift_body ((call_iff g.lookup).mpr rfl)

private theorem resume_iff {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step CallFrame.limeNoHost (limeConfig s caller site (.resume stack (op :: rest))) dst ↔
      ∃ out, Prefix.Reduce site.outer.locals stack op out ∧ dst = limeConfig s caller site (afterOp rest out) := by
  have stays {out} : PureStep site.outer.module.types
      [.label site.arity [] (values stack ++ emit op :: rest.map emit)] out → False := by
    cases op <;> exact label_stays rfl (by simp [emit, Prefix.emit, limeSyntax]) (by simp [emit, Prefix.emit, limeSyntax])
      (by simp [emit, Prefix.emit, limeSyntax])
  constructor
  · intro h
    obtain ⟨mid, move, eq⟩ := read_body stays h
    obtain ⟨out, reduce, rfl⟩ := Prefix.lime_step_iff.mp move
    exact ⟨out, reduce, eq.trans (by rw [limeConfig, after_code])⟩
  · rintro ⟨out, reduce, rfl⟩
    have step := Prefix.lime_step_iff (s := s) (f := site.outer)
      (tail := rest.map emit) |>.mpr ⟨out, reduce, rfl⟩
    simp only [limeConfig, after_code]
    exact lift_body step

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site}
    {a b : State} (g : LimeGuard s site) (edge : Edge site a b) :
    Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) := by
  cases invert edge with
  | @call a b _ inner =>
    have step := CallFrame.lime_sound (caller := site.outer) g.allocated inner
    simp only [limeConfig, attach_code]
    have lifted : Step CallFrame.limeNoHost
        ⟨s, site.outer, CallFrame.limeCode site.address site.callee a ++ site.continuation.map emit⟩
        ⟨s, site.outer, CallFrame.limeCode site.address site.callee b ++ site.continuation.map emit⟩ := by
      simpa only [values, List.map_nil, List.nil_append] using Step.context step [] (site.continuation.map emit)
    exact lift_body lifted
  | ground rule =>
    cases rule with
    | resolve => exact (resolve_iff g).mpr rfl
    | resume h => exact resume_iff.mpr ⟨_, h, rfl⟩
    | discard h =>
      have move := Prefix.lime_discard_iff (s := s) (f := site.outer) emit |>.mpr ⟨_, _, h, rfl⟩
      simp only [limeConfig, trapped_code]
      exact lift_body move
    | boundary h => exact Nested.lime_sound g.allocated (Nested.fact h)

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site}
    {a : State} {dst : Config H} (g : LimeGuard s site) (ready : Admitted site a)
    (step : Step CallFrame.limeNoHost (limeConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = limeConfig s caller site out := by
  cases a with
  | call saved args => exact ⟨_, fact (.resolve saved args), (resolve_iff g).mp step⟩
  | active q =>
    obtain ⟨mid, inner, eq⟩ := read_body (active_label_stays ready.1) step
    obtain ⟨mid', move, rfl⟩ := CallContinuation.Proofs.Lime1.active_strip ready.1 inner
    obtain ⟨out, edge, rfl⟩ := (CallFrame.lime_step_iff g.allocated ready.2.1).mp move
    exact ⟨attach site out, call ready.1 edge, eq.trans (by rw [limeConfig, attach_code]; rfl)⟩
  | resume stack rest =>
    cases rest with
    | nil => exact (ready.1 rfl).elim
    | cons op rest =>
      obtain ⟨out, move, eq⟩ := resume_iff.mp step
      exact ⟨_, fact (.resume move), eq⟩
  | trapped stack rest =>
    have nonempty : stack ≠ [] ∨ rest.map emit ≠ [] := by simpa [Admitted] using ready
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := stack) (head := .trap) rfl (by simp) (by simp) (fun _ => nonempty)) step
    obtain ⟨kept, rest, cut, rfl⟩ := (Prefix.lime_discard_iff (f := site.outer) emit).mp move
    exact ⟨_, fact (.discard cut), eq.trans (by rw [limeConfig, trapped_code])⟩
  | boundary phase =>
    have guard := nested_ready (site := site) ready
    obtain ⟨out, edge, eq⟩ := (Nested.lime_step_iff g.allocated guard).mp step
    exact ⟨_, fact (.boundary (boundary_ground ready edge)), eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Proofs.Lime1
