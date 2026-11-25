module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Lime1
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value AdminInstr)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {H : Type} {s : Store H} {program : Graph.Program}
  {call : Invocation} {cont : Continuation} {outer : Frame}

private theorem wrap_step_iff {inner dst : Config H}
    (stays : ∀ out, ¬ PureStep inner.frame.module.types
      [.label cont.owner.declaration.results.length [] inner.code] out) :
    Step CallFrame.limeNoHost (cont.limeWrap outer inner) dst ↔
      ∃ mid, Step CallFrame.limeNoHost inner mid ∧ dst = cont.limeWrap outer mid := by
  obtain ⟨s, f, code⟩ := inner
  constructor
  · intro step
    rcases Computed.lime_body_step_cases step with ⟨mid, move, eq⟩ | ⟨out, pop, _⟩
    · exact ⟨mid, move, eq⟩
    · exact (stays out pop).elim
  · rintro ⟨⟨s', f', code'⟩, move, rfl⟩
    exact .frame (.label move _ []) _ outer

private theorem wrap_exact {a b : Config H}
    (stays : ∀ out, ¬ PureStep a.frame.module.types [.label cont.owner.declaration.results.length [] a.code] out)
    (step : ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :
    ∀ dst, Step CallFrame.limeNoHost (cont.limeWrap outer a) dst ↔ dst = cont.limeWrap outer b := by
  intro dst
  rw [wrap_step_iff stays]
  simp only [step, exists_eq_left]

theorem resolution_step_iff {site : Indirect.Site} {caller : Frame} {selector : BitVec 32}
    {stack : List Value} {out : Outcome} {dst : Config H}
    (checked : site.check program caller = true) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s caller = some site.table) (resolved : site.resolve program selector = some out) :
    Step CallFrame.limeNoHost
      (cont.limeWrap outer (limeSource s caller site selector stack (cont.code.map Graph.limeEmit))) dst ↔
      dst = cont.limeWrap outer (limeResolved s caller stack (cont.code.map Graph.limeEmit) out) :=
  wrap_exact (fun out => Indirect.lime_lookup_stays _ out) (fun _ => Indirect.lime_step_iff checked allocated tableFound resolved) dst

theorem prefix_exact (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) :
    (cont.limePrefix call s outer).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  refine map_chain (cont.limeWrap outer) (Context.lime_prefix_exact checked allocated tableFound) ?_
  intro a mem b exactStep
  change a ∈ [limeSource s call.caller call.site call.selector (call.saved ++ call.args) (cont.code.map Graph.limeEmit),
    limeResolved s call.caller (call.saved ++ call.args) (cont.code.map Graph.limeEmit) (.resolved call.address)] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact wrap_exact (fun out => Indirect.lime_lookup_stays _ out) exactStep
  · exact wrap_exact (fun out => Indirect.lime_invoke_stays _ out) exactStep

private theorem handoff (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (result : Nested.Result) :
    cont.limeConfig call s outer (.callee (.done result)) =
      cont.limeConfig call s outer (.caller (cont.resume call.caller call.saved result)) := by
  cases result <;> simp only [Continuation.limeConfig, Continuation.limeWrap, Invocation.limeCallee,
    Graph.limeConfig, Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, Continuation.resume,
    Continuation.target, Graph.currentFrame, Graph.LabelKind.arity, Graph.LabelKind.cont,
    Graph.Body.render, Nested.resultCode, values, List.map_append, List.append_assoc, List.singleton_append]
  all_goals rw [← continuation.module_eq]

private theorem callee_step (checked : call.Checked program) (allocated : program.LimeAllocated s)
    {a : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step CallFrame.limeNoHost (cont.limeConfig call s outer (.callee a)) dst ↔
      ∃ out, program.FrameEdge call.address a out ∧ dst = cont.limeConfig call s outer (.callee out) := by
  obtain ⟨n, f, body, render⟩ := Context.Proofs.Lime1.frame_shape (call := call) live
  have stays (out : List Admin) :
      ¬ PureStep call.caller.module.types
        [.label cont.owner.declaration.results.length [] (call.limeCallee s (cont.code.map Graph.limeEmit) a).code] out := by
    simp only [Invocation.limeCallee, render, List.append_assoc, List.singleton_append]
    exact Computed.lime_label_stays (head := .frame n f body) rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (cont.limeWrap outer (call.limeCallee s (cont.code.map Graph.limeEmit) a)) dst ↔ _
  rw [wrap_step_iff stays]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨out, move, rfl⟩ := (Context.lime_frame_step_iff checked allocated ready live).mp step
    exact ⟨out, move, rfl⟩
  · rintro ⟨out, move, rfl⟩
    exact ⟨_, (Context.lime_frame_step_iff checked allocated ready live).mpr ⟨_, move, rfl⟩, rfl⟩

theorem run_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (tableFound : frameTable s call.caller = some call.site.table) {dst : Config H} :
    Steps CallFrame.limeNoHost
      (cont.limeWrap outer (limeSource s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.limeEmit))) dst ↔
      dst ∈ (cont.limePrefix call s outer).dropLast ∨
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.limeConfig call s outer out := by
  have exactPrefix := prefix_exact (cont := cont) (outer := outer) checked allocated tableFound
  have path := prefix_run_iff (dst := dst) (native := Step CallFrame.limeNoHost)
    (cont.limePrefix call s outer).dropLast (cont.limeConfig call s outer (.callee call.entered)) (by exact exactPrefix)
  exact path.trans (or_congr Iff.rfl
    (entered_run_iff checked continuation (cont.limeConfig call s outer) _
      (fun h live => callee_step checked allocated h live)
      (fun ready resolved => Graph.lime_resolved_frame_step_iff checked.graph allocated continuation.found rfl ready resolved)
      (handoff continuation)))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs.Lime1
