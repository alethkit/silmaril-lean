module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open StraightLine
open Computed (limeSyntax)
open Computed.Sequence (limeSource)

private abbrev emit {site : Sequence.Site} := Sequence.emit (site := site) limeSyntax

private theorem label_result {site : Site} {q : Sequence.State site.body} {out : List Admin}
    (ready : Sequence.Admitted site.body q) (pop : PureStep site.frame.module.types [.label site.arity [] (Sequence.limeCode site.body q)] out) :
    ∃ result, Finished site q result ∧ out = Nested.resultCode values .trap result := by
  cases q with
  | active i callee rest =>
    exact (StraightLine.lime_active_label_stays ready.1 pop).elim
  | running stack rest =>
    cases rest with
    | nil =>
      have h : PureStep site.frame.module.types [.label site.arity [] (Nested.resultCode values .trap (.values stack))] out := by
        simpa only [Sequence.limeCode, Sequence.render, List.map_nil, List.append_nil, Nested.resultCode] using pop
      exact ⟨.values stack, .values stack, Nested.lime_label_result h⟩
    | cons op rest =>
      cases op with
      | numeric op =>
        have h := pop
        change PureStep site.frame.module.types [.label site.arity [] ((values stack ++ emit (.numeric op) :: rest.map emit))] out at h
        cases op <;> exact (Computed.lime_label_stays (stack := stack) rfl (by simp [emit, Sequence.emit, Computed.Prefix.emit, limeSyntax])
          (by simp [emit, Sequence.emit, Computed.Prefix.emit, limeSyntax]) (by simp [emit, Sequence.emit, Computed.Prefix.emit, limeSyntax]) h).elim
      | call i =>
        have h := pop
        change PureStep site.frame.module.types [.label site.arity [] ((values stack ++ emit (.call i) :: rest.map emit))] out at h
        exact (Computed.lime_label_stays (stack := stack) (head := .source (.call (site.body.target i).index))
          rfl (by simp) (by simp) (by simp) h).elim
  | trapped stack rest =>
    by_cases unfinished : ¬ (stack = [] ∧ rest = [])
    · have h := pop
      change PureStep site.frame.module.types [.label site.arity [] ((values stack ++ .trap :: rest.map emit))] out at h
      exact (Computed.lime_label_stays (stack := stack) (head := .trap) rfl (by simp) (by simp)
        (fun _ => by simpa using not_and_or.mp unfinished) h).elim
    · obtain ⟨rfl, rfl⟩ := not_not.mp unfinished
      exact ⟨.trap, .trap, Nested.lime_label_result pop⟩

theorem body_expression (p : Program) :
    expression p.limeFunc.body = Sequence.limeCode p.site.body (.running [] p.code) := by
  change (p.body limeSource).map Execution.Runtime.AdminInstr.source = p.body limeSyntax
  simp only [Program.body, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | numeric op => cases op <;> rfl
  | call => rfl

private theorem enter_iff {H : Type} {s : Store H} {caller : Frame}
    {p : Program} {dst : Config H} (g : LimeGuard s caller p) :
    Step CallFrame.limeNoHost (limeConfig s caller p.site .invoke) dst ↔
      dst = limeConfig s caller p.site (.label (.running [] p.code)) := by
  have count : p.site.args.length = p.site.type.params.length := by
    simpa [Site.type] using congrArg List.length g.typed.args
  have enter := CallFrame.lime_invoke_wasm_exact (caller := caller) (dst := dst) g.allocated count
  rw [body_expression] at enter
  exact enter

theorem sound {H : Type} {s : Store H} {caller : Frame}
    {p : Program} {a b : State p.site} (g : LimeGuard s caller p) (edge : Edge p a b) :
    Step CallFrame.limeNoHost (limeConfig s caller p.site a) (limeConfig s caller p.site b) := by
  cases invert edge with
  | body move => exact .frame (.label (Sequence.lime_sound g.body move) _ []) _ caller
  | ground move =>
    cases move with
    | resolve => exact (Computed.lime_direct_call_iff g.resolves).mpr rfl
    | enter => exact (enter_iff g).mpr rfl
    | leaveLabel result =>
      cases result with
      | values stack =>
        have exit : Step CallFrame.limeNoHost
            ⟨s, caller, [.frame p.site.arity p.site.frame [.label p.site.arity [] (values stack)]]⟩
            (limeConfig s caller p.site (.exit (.values stack))) :=
          .frame (.pure s p.site.frame (.labelDone _ [] stack)) _ caller
        simpa only [limeConfig, limeCode, render, Sequence.limeCode, Sequence.render, List.map_nil, List.append_nil] using exit
      | trap => exact .frame (.pure s p.site.frame (.labelTrap _ [])) _ caller
    | leaveFrame result arity =>
      cases result with
      | values stack => exact .pure s caller (.frameDone _ _ stack arity)
      | trap => exact .pure s caller (.frameTrap _ _)

theorem readback {H : Type} {s : Store H} {caller : Frame}
    {p : Program} {a : State p.site} {dst : Config H} (g : LimeGuard s caller p)
    (ready : Admitted p.site a) (step : Step CallFrame.limeNoHost (limeConfig s caller p.site a) dst) :
    ∃ out, Edge p a out ∧ dst = limeConfig s caller p.site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (Computed.lime_direct_call_iff g.resolves).mp step⟩
  | invoke => exact ⟨_, fact .enter, (enter_iff g).mp step⟩
  | label q =>
    rcases Computed.lime_body_step_cases step with ⟨mid, move, eq⟩ | ⟨_, pop, eq⟩
    · obtain ⟨out, edge, rfl⟩ := (Sequence.lime_step_iff g.body ready).mp move
      exact ⟨.label out, underLabel edge, eq⟩
    · obtain ⟨result, finished, rfl⟩ := label_result ready pop
      exact ⟨.exit result, fact (.leaveLabel finished), eq⟩
  | exit result =>
    exact ⟨.done result, fact (.leaveFrame result (result_arity ready)), Nested.lime_frame_result  step⟩
  | done result => exact (Nested.lime_result_stuck step).elim

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs.Lime1
