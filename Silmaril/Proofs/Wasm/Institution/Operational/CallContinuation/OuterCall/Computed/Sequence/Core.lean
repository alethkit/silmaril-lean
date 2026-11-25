module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs.Core

open Execution.Core
open Wasm.SingleThreaded.Det (noHost)
open Execution.Runtime (FuncAddr Value)
open Wasm.Numerics (Profile)
open Wasm.Validation (Expand Ty)
open Computed.Proofs.Core (core_func lift_body read_body label_stays call_iff)

private theorem frame_init (site : Site) :
    Frame.forCall site.outerModule.toCore (site.args.map Value.toCore) site.coreFunc.locals = site.frame.toCore := by
  simp only [Frame.forCall, Site.coreFunc, Site.frame, Execution.Runtime.Frame.toCore,
    List.map_append, List.map_map]
  congr 2
  change (site.locals.map Wasm.V1.ValType.toCore).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  cases t <;> rfl

private theorem body_expression (site : Site) :
    expression site.coreFunc.body = site.body coreSyntax := by
  change (site.body coreSource).map Admin.plain = _
  simp only [Site.body, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | arg op => cases op <;> rfl
  | call | nop => rfl

private theorem enter_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {dst : Config H} (g : CoreGuard s caller site) :
    Step P noHost (coreConfig s caller site .invoke) dst ↔ dst = coreConfig s caller site (.args [] site.prefixCode) := by
  have sig : Expand site.type.toDefType (.func (Ty.ofList (site.params.map Ty.num))
      (Ty.ofList (site.inner.result.toList.map Ty.num))) :=
    Expand.iff.mpr (Wasm.V1.FuncType.toDefType_expand _)
  have count : (site.args.map Value.toCore).length = (Ty.ofList (site.params.map Ty.num)).length := by
    simpa [Ty.length_ofList] using congrArg List.length g.typed.outerArgs
  have target : (⟨s, caller.toCore, [.frame (Ty.ofList (site.inner.result.toList.map Ty.num)).length
      (Frame.forCall site.outerModule.toCore (site.args.map Value.toCore) site.coreFunc.locals)
      [.label (Ty.ofList (site.inner.result.toList.map Ty.num)).length [] (expression site.coreFunc.body)]]⟩ :
        Config H) = coreConfig s caller site (.args [] site.prefixCode) := by
    rw [frame_init, Ty.length_ofList, List.length_map, body_expression]
    rfl
  constructor
  · intro h
    exact (Step.callRef_wasm_inv_exact (r := .callRefType site.type.toDefType)
      (code := site.coreFunc) (by trivial) g.outerAlloc rfl sig count h).trans target
  · rintro rfl
    rw [← target]
    exact .callRefFunc (c := .callRefType site.type.toDefType) trivial g.outerAlloc sig count rfl

private theorem op_stays {n : Nat} {stack : List Value} {op : Prefix.Op} {tail out : List Admin}
    (h : LabelExit n [] (coreValues stack ++ Prefix.emit coreSyntax op :: tail) out) : False := by
  cases op <;> exact label_stays rfl (by simp [Prefix.emit, coreSyntax]) (by simp [Prefix.emit, coreSyntax])
    (by simp [Prefix.emit, coreSyntax, Admin.IsReturnCallRef]) (by simp [Prefix.emit, coreSyntax])
    (by simp [Prefix.emit, coreSyntax]) h

private theorem inner_start_code (site : Site) (stack : List Value) :
    coreCode site (.nested (innerStart stack)) = [.frame site.arity site.frame.toCore
      [.label site.arity [] (coreValues stack ++
        [.ref (.func site.innerAddr.value), .callRefType site.inner.type.toDefType, .plain .nop])]] := by
  simp only [coreCode, render, innerStart, Nested.coreCode, Nested.render, CallContinuation.coreCode,
    CallContinuation.render, CallFrame.coreCode, List.nil_append, List.append_assoc, List.cons_append, List.nil_append]

private theorem resolveInner_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {stack : List Value} {dst : Config H} (g : CoreGuard s caller site) :
    Step P noHost (coreConfig s caller site (.args stack [])) dst ↔
      dst = coreConfig s caller site (.nested (innerStart stack)) := by
  constructor
  · intro h
    obtain ⟨mid, step, eq⟩ := read_body (label_stays (head := .plain (.call site.innerIndex))
      (stack := stack.map Value.toCore) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
      (by simp) (by simp)) h
    have read := (call_iff g.innerLookup g.innerAlloc).mp step
    exact eq.trans (by rw [read, coreConfig, inner_start_code]; rfl)
  · rintro rfl
    simp only [coreConfig, inner_start_code]
    exact lift_body (caller := caller.toCore) (n := site.arity) ((call_iff g.innerLookup g.innerAlloc
        (stack := stack) (tail := [.plain .nop])).mpr rfl)

private theorem eval_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {dst : Config H} :
    Step P noHost (coreConfig s caller site (.args stack (op :: rest))) dst ↔
      ∃ ans, Prefix.Reduce site.frame.locals stack op ans ∧ dst = coreConfig s caller site (afterOp rest ans) := by
  constructor
  · intro h
    obtain ⟨mid, step, eq⟩ := read_body
      (op_stays (stack := stack) (op := op) (tail := (pending rest).map (site.pendingOp coreSyntax))) h
    obtain ⟨ans, reduce, rfl⟩ := Prefix.core_step_iff.mp step
    exact ⟨ans, reduce, eq.trans (by cases ans <;> rfl)⟩
  · rintro ⟨ans, reduce, rfl⟩
    have step := Prefix.core_step_iff (s := s) (P := P) (f := site.frame)
      (tail := (pending rest).map (site.pendingOp coreSyntax)) |>.mpr ⟨ans, reduce, rfl⟩
    cases ans <;> exact lift_body step

private theorem render_trap (site : Site) (stack : List Value) (rest : List Pending) :
    coreCode site (trapState stack rest) = coreCode site (.trap stack rest) := by
  cases stack <;> cases rest <;> rfl

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {a b : State} (g : CoreGuard s caller site) (edge : Edge site a b) :
    Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) := by
  cases invert edge with
  | nest h => exact Nested.core_sound g.innerAlloc h
  | ground rule =>
    cases rule with
    | resolve => exact (call_iff g.outerLookup g.outerAlloc).mpr rfl
    | enter => exact (enter_iff g).mpr rfl
    | arg h => exact eval_iff.mpr ⟨_, h, rfl⟩
    | trap h => exact eval_iff.mpr ⟨_, h, rfl⟩
    | resolveInner => exact (resolveInner_iff g).mpr rfl
    | discard cut =>
      have step := Prefix.core_discard_iff (s := s) (P := P) (f := site.frame)
        (site.pendingOp coreSyntax) |>.mpr ⟨_, _, cut, rfl⟩
      simp only [coreConfig, render_trap]
      exact lift_body (caller := caller.toCore) (n := site.arity) step

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {a : State} {dst : Config H} (g : CoreGuard s caller site) (ready : Admitted site a)
    (step : Step P noHost (coreConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = coreConfig s caller site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (call_iff g.outerLookup g.outerAlloc).mp step⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp step⟩
  | nested q =>
    obtain ⟨out, edge, eq⟩ := (Nested.core_step_iff g.innerAlloc ready).mp step
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
    have nonempty : stack.map Value.toCore ≠ [] ∨ tail.map (site.pendingOp coreSyntax) ≠ [] := by
      simpa [Admitted] using ready
    obtain ⟨mid, move, eq⟩ := read_body (label_stays (head := .trap) (stack := stack.map Value.toCore)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (fun _ => nonempty)) step
    obtain ⟨kept, rest, cut, rfl⟩ := (Prefix.core_discard_iff (f := site.frame) (site.pendingOp coreSyntax)).mp move
    refine ⟨trapState kept rest, fact (.discard cut), ?_⟩
    simp only [coreConfig, render_trap]
    exact eq

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Proofs.Core
