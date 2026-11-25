module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Core
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open Execution
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H} {program : Graph.Program}
  {call : Invocation} {cont : Continuation} {outer : Runtime.Frame}

private theorem wrap_step_iff {inner dst : Config H}
    (stays : ∀ out, ¬ LabelExit cont.owner.declaration.results.length [] inner.code out) :
    Step P noHost (cont.coreWrap outer inner) dst ↔
      ∃ mid, Step P noHost inner mid ∧ dst = cont.coreWrap outer mid := by
  obtain ⟨s, f, code⟩ := inner
  constructor
  · intro step
    rcases Computed.core_body_step_cases step with ⟨mid, move, eq⟩ | ⟨out, pop, _⟩
    · exact ⟨mid, move, eq⟩
    · exact (stays out pop).elim
  · rintro ⟨⟨s', f', code'⟩, move, rfl⟩
    exact .ctxtFrame (.ctxtLabel move)

private theorem wrap_exact {a b : Config H}
    (stays : ∀ out, ¬ LabelExit cont.owner.declaration.results.length [] a.code out)
    (step : ∀ dst, Step P noHost a dst ↔ dst = b) :
    ∀ dst, Step P noHost (cont.coreWrap outer a) dst ↔ dst = cont.coreWrap outer b := by
  intro dst
  rw [wrap_step_iff stays]
  simp only [step, exists_eq_left]

private def pending : Indirect.Phase → Prop
  | .start | .lookup | .cast _ | .call _ => True
  | _ => False

private theorem lookup_stays {site : Indirect.Site} {selector : BitVec 32}
    {stack : List Value} {rest : List Admin} {phase : Indirect.Phase} (h : pending phase)
    (n : Nat) (out : List Admin) : ¬ LabelExit n [] (coreValues stack ++ site.coreCode selector phase ++ rest) out := by
  let vs := stack.map Value.toCore
  cases phase with
  | start =>
    intro pop
    apply Computed.core_label_stays (stack := vs ++ [Val.i32 selector])
      (head := .plain (.callIndirect tableIndex site.typeIndex)) (rest := rest)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
    simpa only [coreValues, List.append_assoc, Site.coreCode, vals, List.map_append, List.map_singleton,
      List.cons_append, List.nil_append, constI32] using pop
  | lookup =>
    intro pop
    apply Computed.core_label_stays (stack := vs ++ [Val.i32 selector])
      (head := .plain (.tableGet tableIndex)) (rest := site.coreCast :: site.coreCall :: rest)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
    simpa only [coreValues, List.append_assoc, Site.coreCode, vals, List.map_append, List.map_singleton,
      List.cons_append, List.nil_append, constI32] using pop
  | cast entry =>
    intro pop
    apply Computed.core_label_stays (stack := vs ++ [.ref (coreRef entry)])
      (head := site.coreCast) (rest := site.coreCall :: rest)
      rfl (by simp [Site.coreCast]) (by simp [Site.coreCast])
      (by simp [Site.coreCast, Admin.IsReturnCallRef]) (by simp [Site.coreCast]) (by simp [Site.coreCast])
    simpa only [coreValues, List.append_assoc, Site.coreCode, vals, List.map_append, List.map_singleton,
      List.cons_append, List.nil_append, Val.toAdmin] using pop
  | call entry =>
    intro pop
    apply Computed.core_label_stays (stack := vs ++ [.ref (coreRef entry)])
      (head := site.coreCall) (rest := rest)
      rfl (by simp [Site.coreCall]) (by simp [Site.coreCall])
      (by simp [Site.coreCall, Admin.IsReturnCallRef]) (by simp [Site.coreCall]) (by simp [Site.coreCall])
    simpa only [coreValues, List.append_assoc, Site.coreCode, vals, List.map_append, List.map_singleton,
      List.cons_append, List.nil_append, Val.toAdmin] using pop
  | boundsTrap | mismatchTrap | nullTrap => exact h.elim

theorem resolution_prefix_exact {site : Indirect.Site} {caller : Runtime.Frame} {out : Outcome}
    {selector : BitVec 32} {stack : List Value} {addr : Nat}
    (checked : site.check program caller = true) (allocated : program.CoreAllocated s)
    (tableFound : s.table? caller.toCore tableIndex = some (addr, site.table.toCore))
    (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Step P noHost (cont.coreWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) a)) dst ↔
        dst = cont.coreWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) b)) := by
  have chain := Indirect.core_trace_exact (P := P) (stack := stack) (rest := cont.code.map Graph.coreEmit)
    checked allocated tableFound resolved
  have live (a : Indirect.Phase) (mem : a ∈ (out.coreTrace).dropLast) : pending a := by
    cases out <;>
      simp only [Outcome.coreTrace, List.cons_append, List.nil_append, List.dropLast_cons_cons, List.dropLast_singleton,
        List.mem_cons, List.not_mem_nil, or_false] at mem <;>
      rcases mem with rfl | rfl | rfl | rfl <;> trivial
  let render a := cont.coreWrap outer (Indirect.coreConfig s caller site selector stack
    (cont.code.map Graph.coreEmit) a)
  apply (List.isChain_map (R := fun a b : Config H => ∀ dst, Step P noHost a dst ↔ dst = b) render).mp
  exact map_chain render chain (fun a mem b exactStep => wrap_exact (cont := cont) (outer := outer)
    (fun out => lookup_stays (live a mem) _ out) exactStep)

theorem prefix_exact (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) :
    (cont.corePrefix call s outer).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  let inner := Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
    (cont.code.map Graph.coreEmit)
  refine map_chain (cont.coreWrap outer) (Context.core_prefix_exact (P := P) checked allocated tableFound) ?_
  intro a mem b exactStep
  change a ∈ [inner .start, inner .lookup, inner (.cast (some call.address)), inner (.call (some call.address))] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · exact wrap_exact (fun out => lookup_stays (phase := .start) trivial _ out) exactStep
  · exact wrap_exact (fun out => lookup_stays (phase := .lookup) trivial _ out) exactStep
  · exact wrap_exact (fun out => lookup_stays (phase := .cast (some call.address)) trivial _ out) exactStep
  · exact wrap_exact (fun out => lookup_stays (phase := .call (some call.address)) trivial _ out) exactStep

private theorem handoff (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (result : Nested.Result) :
    cont.coreConfig call s outer (.callee (.done result)) =
      cont.coreConfig call s outer (.caller (cont.resume call.caller call.saved result)) := by
  cases result <;> simp only [Continuation.coreConfig, Continuation.coreWrap, Invocation.coreCallee,
    Graph.coreConfig, Graph.Phase.render, Graph.Phase.renderAt, Graph.coreAdmin, Continuation.resume,
    Continuation.target, Graph.currentFrame, Graph.LabelKind.arity, Graph.LabelKind.cont,
    Graph.Body.render, Nested.resultCode, coreValues, vals_append, List.map_append,
    List.append_assoc, List.singleton_append]
  all_goals rw [← continuation.module_eq]

private theorem callee_step (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {a : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step P noHost (cont.coreConfig call s outer (.callee a)) dst ↔
      ∃ out, program.FrameEdge call.address a out ∧ dst = cont.coreConfig call s outer (.callee out) := by
  obtain ⟨n, f, body, render⟩ := Context.Proofs.Core.frame_shape (call := call) live
  have stays (out : List Admin) :
      ¬ LabelExit cont.owner.declaration.results.length []
        (call.coreCallee s (cont.code.map Graph.coreEmit) a).code out := by
    simp only [Invocation.coreCallee, render, List.append_assoc, List.singleton_append]
    exact Computed.core_label_stays (head := .frame n f body) rfl (by simp) (by simp)
      (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (cont.coreWrap outer (call.coreCallee s (cont.code.map Graph.coreEmit) a)) dst ↔ _
  rw [wrap_step_iff stays]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨out, move, rfl⟩ := (Context.core_frame_step_iff checked allocated ready live).mp step
    exact ⟨out, move, rfl⟩
  · rintro ⟨out, move, rfl⟩
    exact ⟨_, (Context.core_frame_step_iff checked allocated ready live).mpr ⟨_, move, rfl⟩, rfl⟩

theorem run_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore))
    {dst : Config H} :
    Steps P noHost
      (cont.coreWrap outer (Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.coreEmit) .start)) dst ↔
      dst ∈ (cont.corePrefix call s outer).dropLast ∨
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.coreConfig call s outer out := by
  have exactPrefix := prefix_exact (P := P) (cont := cont) (outer := outer) checked allocated tableFound
  have path := prefix_run_iff (dst := dst) (native := Step P noHost)
    (cont.corePrefix call s outer).dropLast (cont.coreConfig call s outer (.callee call.entered)) (by exact exactPrefix)
  exact path.trans (or_congr Iff.rfl
    (entered_run_iff checked continuation (cont.coreConfig call s outer) _
      (fun h live => callee_step checked allocated h live)
      (fun ready resolved => Graph.core_resolved_frame_step_iff checked.graph allocated continuation.found rfl ready resolved)
      (handoff continuation)))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs.Core
