module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame FuncAddr Value)
open Computed.Proofs.Lime1 (lift_body read_body label_stays call_iff)

private theorem body_expression (site : Site) :
    expression site.limeFunc.body = site.body limeSyntax := by
  change (site.body limeSource).map Execution.Runtime.AdminInstr.source = _
  simp only [Site.body, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | arg op => cases op <;> rfl
  | call | nop => rfl

private theorem enter_iff {H : Type} {s : Store H} {caller : Frame} {site : Site} {dst : Config H}
    (g : LimeGuard s caller site) :
    Step CallFrame.limeNoHost (limeConfig s caller site .invoke) dst ↔
      dst = limeConfig s caller site (.args [] site.prefixCode) := by
  have count : site.args.length = site.type.params.length := by
    simpa [Site.type] using congrArg List.length g.typed.outerArgs
  have h := CallFrame.lime_invoke_wasm_exact (caller := caller) (dst := dst) g.outerAlloc count
  rw [body_expression] at h
  exact h

private theorem op_stays {types : List Wasm.Lime1.FuncType} {n : Nat}
    {stack : List Value} {op : Prefix.Op} {tail out : List Admin}
    (h : PureStep types [.label n [] (values stack ++ Prefix.emit limeSyntax op :: tail)] out) : False := by
  cases op <;> exact label_stays rfl (by simp [Prefix.emit, limeSyntax]) (by simp [Prefix.emit, limeSyntax])
    (by simp [Prefix.emit, limeSyntax]) h

private theorem inner_start_code (site : Site) (stack : List Value) :
    limeCode site (.nested (innerStart stack)) = [.frame site.arity site.frame
      [.label site.arity [] (values stack ++ [.invoke site.innerAddr, .source .nop])]] := by
  simp only [limeCode, render, innerStart, Nested.limeCode, Nested.render, CallContinuation.limeCode,
    CallContinuation.render, CallFrame.limeCode, CallFrame.legacyCode, values, List.nil_append,
    List.append_assoc, List.cons_append]

private theorem resolveInner_iff {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {stack : List Value} {dst : Config H} (g : LimeGuard s caller site) :
    Step CallFrame.limeNoHost (limeConfig s caller site (.args stack [])) dst ↔
      dst = limeConfig s caller site (.nested (innerStart stack)) := by
  constructor
  · intro h
    obtain ⟨mid, step, eq⟩ := read_body (label_stays (head := .source (.call site.innerIndex))
      (stack := stack) rfl (by simp) (by simp) (by simp)) h
    have read := (call_iff g.innerLookup).mp step
    exact eq.trans (by rw [read, limeConfig, inner_start_code]; rfl)
  · rintro rfl
    simp only [limeConfig, inner_start_code]
    exact lift_body (caller := caller) (n := site.arity) ((call_iff g.innerLookup
        (stack := stack) (tail := [.source .nop])).mpr rfl)

private theorem eval_iff {H : Type} {s : Store H} {caller : Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step CallFrame.limeNoHost (limeConfig s caller site (.args stack (op :: rest))) dst ↔
      ∃ ans, Prefix.Reduce site.frame.locals stack op ans ∧ dst = limeConfig s caller site (afterOp rest ans) := by
  constructor
  · intro h
    obtain ⟨mid, step, eq⟩ := read_body
      (op_stays (stack := stack) (op := op) (tail := (pending rest).map (site.pendingOp limeSyntax))) h
    obtain ⟨ans, reduce, rfl⟩ := Prefix.lime_step_iff.mp step
    exact ⟨ans, reduce, eq.trans (by cases ans <;> rfl)⟩
  · rintro ⟨ans, reduce, rfl⟩
    have step := Prefix.lime_step_iff (s := s) (f := site.frame)
      (tail := (pending rest).map (site.pendingOp limeSyntax)) |>.mpr ⟨ans, reduce, rfl⟩
    cases ans <;> exact lift_body step

private theorem render_trap (site : Site) (stack : List Value) (rest : List Pending) :
    limeCode site (trapState stack rest) = limeCode site (.trap stack rest) := by
  cases stack <;> cases rest <;> rfl

theorem sound {H : Type} {s : Store H} {caller : Frame} {site : Site} {a b : State}
    (g : LimeGuard s caller site) (edge : Edge site a b) :
    Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) := by
  cases invert edge with
  | nest h => exact Nested.lime_sound g.innerAlloc h
  | ground rule =>
    cases rule with
    | resolve => exact (call_iff g.outerLookup).mpr rfl
    | enter => exact (enter_iff g).mpr rfl
    | arg h => exact eval_iff.mpr ⟨_, h, rfl⟩
    | trap h => exact eval_iff.mpr ⟨_, h, rfl⟩
    | resolveInner => exact (resolveInner_iff g).mpr rfl
    | discard cut =>
      have step := Prefix.lime_discard_iff (s := s) (f := site.frame)
        (site.pendingOp limeSyntax) |>.mpr ⟨_, _, cut, rfl⟩
      simp only [limeConfig, render_trap]
      exact lift_body (caller := caller) (n := site.arity) step

theorem readback {H : Type} {s : Store H} {caller : Frame} {site : Site} {a : State} {dst : Config H}
    (g : LimeGuard s caller site) (ready : Admitted site a)
    (step : Step CallFrame.limeNoHost (limeConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = limeConfig s caller site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (call_iff g.outerLookup).mp step⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp step⟩
  | nested q =>
    obtain ⟨out, edge, eq⟩ := (Nested.lime_step_iff g.innerAlloc ready).mp step
    exact ⟨.nested out, delegate edge, eq⟩
  | args stack rest =>
    cases rest with
    | nil => exact ⟨_, fact (.resolveInner stack), (resolveInner_iff g).mp step⟩
    | cons op rest =>
      obtain ⟨ans, reduce, rfl⟩ := eval_iff.mp step
      cases ans with
      | values => exact ⟨_, fact (.arg reduce), rfl⟩
      | trap => exact ⟨_, fact (.trap reduce), rfl⟩
  | trap stack tail =>
    have nonempty : stack ≠ [] ∨ tail.map (site.pendingOp limeSyntax) ≠ [] := by
      simpa [Admitted] using ready
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (head := .trap) (stack := stack) rfl (by simp) (by simp) (fun _ => nonempty)) step
    obtain ⟨kept, rest, cut, rfl⟩ := (Prefix.lime_discard_iff (f := site.frame) (site.pendingOp limeSyntax)).mp move
    refine ⟨trapState kept rest, fact (.discard cut), ?_⟩
    simp only [limeConfig, render_trap]
    exact eq

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs.Lime1
