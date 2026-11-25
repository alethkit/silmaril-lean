module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs

open Execution
open Execution.Runtime (Value)
open OuterCall (coreValues)
open OuterCall.Computed (coreSyntax limeSyntax)

open Core in
theorem core_label_result {site : Site} {arity : Nat} {q : State site} {out : List Admin}
    (ready : Admitted site q) (pop : LabelExit arity [] (coreCode site q) out) :
    ∃ result, Finished site q result ∧ out = Nested.resultCode coreValues .trap result := by
  cases q with
  | active i callee rest =>
    exact (StraightLine.core_active_label_stays ready.1 pop).elim
  | running stack rest =>
    cases rest with
    | nil =>
      have h : LabelExit arity [] (Nested.resultCode coreValues .trap (.values stack)) out := by
        simpa only [coreCode, render, List.map_nil, List.append_nil, Nested.resultCode] using pop
      exact ⟨.values stack, .values stack, Nested.core_label_result h⟩
    | cons op rest =>
      cases op with
      | numeric op =>
        have h := pop
        change LabelExit arity [] ((coreValues stack ++ emit coreSyntax (.numeric op) :: rest.map (emit coreSyntax))) out at h
        cases op <;> exact (OuterCall.Computed.core_label_stays (stack := stack.map Value.toCore) rfl (by simp [emit, OuterCall.Computed.Prefix.emit, coreSyntax])
          (by simp [emit, OuterCall.Computed.Prefix.emit, coreSyntax]) (by simp [emit, OuterCall.Computed.Prefix.emit, coreSyntax, Admin.IsReturnCallRef])
          (by simp [emit, OuterCall.Computed.Prefix.emit, coreSyntax]) (by simp [emit, OuterCall.Computed.Prefix.emit, coreSyntax]) h).elim
      | call i =>
        have h := pop
        change LabelExit arity [] ((coreValues stack ++ emit coreSyntax (.call i) :: rest.map (emit coreSyntax))) out at h
        exact (OuterCall.Computed.core_label_stays (stack := stack.map Value.toCore) (head := .plain (.call (site.target i).index))
          rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) h).elim
  | trapped stack rest =>
    by_cases unfinished : ¬ (stack = [] ∧ rest = [])
    · have h := pop
      change LabelExit arity [] ((coreValues stack ++ .trap :: rest.map (emit coreSyntax))) out at h
      exact (OuterCall.Computed.core_label_stays (stack := stack.map Value.toCore) (head := .trap)
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp)
        (fun _ => by simpa using not_and_or.mp unfinished) h).elim
    · obtain ⟨rfl, rfl⟩ := not_not.mp unfinished
      exact ⟨.trap, .trap, Nested.core_label_result pop⟩

open Wasm.Lime1.Execution in
theorem lime_label_result {site : Site} {arity : Nat} {q : State site} {out : List Admin}
    (ready : Admitted site q) (pop : PureStep site.frame.module.types [.label arity [] (limeCode site q)] out) :
    ∃ result, Finished site q result ∧ out = Nested.resultCode values .trap result := by
  cases q with
  | active i callee rest =>
    exact (StraightLine.lime_active_label_stays ready.1 pop).elim
  | running stack rest =>
    cases rest with
    | nil =>
      have h : PureStep site.frame.module.types [.label arity [] (Nested.resultCode values .trap (.values stack))] out := by
        simpa only [limeCode, render, List.map_nil, List.append_nil, Nested.resultCode] using pop
      exact ⟨.values stack, .values stack, Nested.lime_label_result h⟩
    | cons op rest =>
      cases op with
      | numeric op =>
        have h := pop
        change PureStep site.frame.module.types [.label arity [] ((values stack ++ emit limeSyntax (.numeric op) :: rest.map (emit limeSyntax)))] out at h
        cases op <;> exact (OuterCall.Computed.lime_label_stays (stack := stack) rfl (by simp [emit, OuterCall.Computed.Prefix.emit, limeSyntax])
          (by simp [emit, OuterCall.Computed.Prefix.emit, limeSyntax]) (by simp [emit, OuterCall.Computed.Prefix.emit, limeSyntax]) h).elim
      | call i =>
        have h := pop
        change PureStep site.frame.module.types [.label arity [] ((values stack ++ emit limeSyntax (.call i) :: rest.map (emit limeSyntax)))] out at h
        exact (OuterCall.Computed.lime_label_stays (stack := stack) (head := .source (.call (site.target i).index))
          rfl (by simp) (by simp) (by simp) h).elim
  | trapped stack rest =>
    by_cases unfinished : ¬ (stack = [] ∧ rest = [])
    · have h := pop
      change PureStep site.frame.module.types [.label arity [] ((values stack ++ .trap :: rest.map (emit limeSyntax)))] out at h
      exact (OuterCall.Computed.lime_label_stays (stack := stack) (head := .trap) rfl (by simp) (by simp)
        (fun _ => by simpa using not_and_or.mp unfinished) h).elim
    · obtain ⟨rfl, rfl⟩ := not_not.mp unfinished
      exact ⟨.trap, .trap, Nested.lime_label_result pop⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs
