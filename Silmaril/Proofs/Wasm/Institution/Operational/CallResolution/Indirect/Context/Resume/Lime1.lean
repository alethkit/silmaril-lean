module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Lime1
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms

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

theorem lime_wrap_step_iff {inner dst : Config H}
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

theorem lime_site_step_iff {inner dst : Config H}
    (stays : ∀ n out, ¬ PureStep inner.frame.module.types [.label n [] inner.code] out) :
    Step CallFrame.limeNoHost (cont.limeSiteWrap outer inner) dst ↔
      ∃ mid, Step CallFrame.limeNoHost inner mid ∧ dst = cont.limeSiteWrap outer mid := by
  have nest := Source.lime_nest_step stays cont.scopes
  rw [Continuation.limeSiteWrap, lime_wrap_step_iff (fun out => nest.1 _ out)]
  constructor
  · rintro ⟨nested, move, rfl⟩
    obtain ⟨mid, step, rfl⟩ := (nest.2 nested).mp move
    exact ⟨mid, step, rfl⟩
  · rintro ⟨mid, step, rfl⟩
    exact ⟨_, (nest.2 _).mpr ⟨mid, step, rfl⟩, rfl⟩

private theorem site_exact {a b : Config H}
    (stays : ∀ n out, ¬ PureStep a.frame.module.types [.label n [] a.code] out)
    (step : ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :
    ∀ dst, Step CallFrame.limeNoHost (cont.limeSiteWrap outer a) dst ↔ dst = cont.limeSiteWrap outer b := by
  intro dst
  rw [lime_site_step_iff stays]
  simp only [step, exists_eq_left]

theorem resolution_step_iff {site : Indirect.Site} {caller : Frame} {selector : BitVec 32}
    {stack : List Value} {out : Outcome} {dst : Config H}
    (checked : site.check program caller = true) (allocated : site.LimeAllocated program s)
    (tableFound : frameTable s caller = some site.table) (resolved : site.resolve program selector = some out) :
    Step CallFrame.limeNoHost
      (cont.limeSiteWrap outer (limeSource s caller site selector stack (cont.code.map Graph.limeEmit))) dst ↔
      dst = cont.limeSiteWrap outer (limeResolved s caller stack (cont.code.map Graph.limeEmit) out) :=
  site_exact Indirect.lime_lookup_stays (fun _ => Indirect.lime_step_allocated_iff checked allocated tableFound resolved) dst

theorem prefix_exact (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) :
    (cont.limePrefix call s outer).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  refine map_chain (cont.limeSiteWrap outer) (Context.lime_prefix_exact checked allocated tableFound) ?_
  intro a mem b exactStep
  change a ∈ [limeSource s call.caller call.site call.selector (call.saved ++ call.args) (cont.code.map Graph.limeEmit),
    limeResolved s call.caller (call.saved ++ call.args) (cont.code.map Graph.limeEmit) (.resolved call.address)] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact site_exact Indirect.lime_lookup_stays exactStep
  · exact site_exact Indirect.lime_invoke_stays exactStep

theorem entry_iff (checked : call.Checked program)
    (allocated : s.funcs[call.address.value]? = some (.wasm call.callee.declaration.type call.callee.declaration.module call.callee.limeFunc)) {dst : Config H} :
    Step CallFrame.limeNoHost (cont.limeSiteWrap outer (Indirect.limeResolved s call.caller (call.saved ++ call.args) (cont.code.map Graph.limeEmit) (.resolved call.address))) dst ↔
      dst = cont.limeConfig call s outer (.callee call.entered) := by
  have entry := site_exact (cont := cont) (outer := outer) Indirect.lime_invoke_stays
    (fun _ => Indirect.lime_enter_at_iff (caller := call.caller) (saved := call.saved)
      (rest := cont.code.map Graph.limeEmit) allocated checked.found checked.resolved checked.typed) dst
  exact entry.trans (by rw [Context.Proofs.Lime1.entered_config]; rfl)

theorem plug_code (blocks : List Block) (saved : List Value) (body : Graph.Body)
    (cfg : Config H) (code : cfg.code = body.render Graph.limeAdmin) :
    (Context.limeNest (Block.scopes blocks saved) cfg).code =
      (Block.plug blocks saved body).render Graph.limeAdmin := by
  induction blocks generalizing saved with
  | nil => exact code
  | cons block rest ih =>
    exact congrArg (fun code => values saved ++
      .label block.result.toList.length [] code :: block.tail.map Graph.limeEmit) (ih [])


private theorem handoff (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (result : Nested.Result) :
    cont.limeConfig call s outer (.callee (.done result)) =
      cont.limeConfig call s outer (.caller (cont.resume call.caller call.saved result)) := by
  let returned := call.limeCallee s (cont.code.map Graph.limeEmit) (.done result)
  have code : returned.code = (cont.deliver call.saved result).render Graph.limeAdmin := by
    cases result <;> simp [returned, Invocation.limeCallee, Continuation.deliver,
      Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, Graph.Body.render,
      Nested.resultCode, values, List.map_append, List.append_assoc]
  have source := plug_code cont.blocks cont.owner.initial (cont.deliver call.saved result) returned code
  have same (scopes : List (Blocks.Context.Scope Graph.Op)) :
      (Context.limeNest scopes returned).store = s ∧
      (Context.limeNest scopes returned).frame = call.caller := by
    induction scopes with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ ih => exact ih
  obtain ⟨store, frame⟩ := same cont.scopes
  change cont.limeWrap outer (Context.limeNest cont.scopes returned) = _
  unfold Continuation.limeWrap
  rw [store, frame]
  change (Context.limeNest cont.scopes returned).code = _ at source
  rw [source]
  simp only [Continuation.limeConfig, Continuation.resume, Continuation.plug, Continuation.target,
    Graph.limeConfig, Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin,
    Graph.LabelKind.arity, Graph.LabelKind.cont, Graph.currentFrame]
  rw [← continuation.module_eq]

private theorem callee_step (checked : call.Checked program) (allocated : program.LimeLinksAllocated s)
    {a : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step CallFrame.limeNoHost (cont.limeConfig call s outer (.callee a)) dst ↔
      ∃ out, program.FrameEdge call.address a out ∧ dst = cont.limeConfig call s outer (.callee out) := by
  obtain ⟨n, f, body, render⟩ := Context.Proofs.Lime1.frame_shape (call := call) live
  have stays (nlabel : Nat) (out : List Admin) :
      ¬ PureStep call.caller.module.types
        [.label nlabel [] (call.limeCallee s (cont.code.map Graph.limeEmit) a).code] out := by
    simp only [Invocation.limeCallee, render, List.append_assoc, List.singleton_append]
    exact Computed.lime_label_stays (head := .frame n f body) rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (cont.limeSiteWrap outer (call.limeCallee s (cont.code.map Graph.limeEmit) a)) dst ↔ _
  rw [lime_site_step_iff stays]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨out, move, rfl⟩ := (Context.Proofs.Lime1.linked_frame_step_iff checked allocated ready live).mp step
    exact ⟨out, move, rfl⟩
  · rintro ⟨out, move, rfl⟩
    exact ⟨_, (Context.Proofs.Lime1.linked_frame_step_iff checked allocated ready live).mpr ⟨_, move, rfl⟩, rfl⟩

theorem entered_run_iff (checked : call.Checked program) (allocated : program.LimeLinksAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {dst : Config H} :
    Steps CallFrame.limeNoHost (cont.limeConfig call s outer (.callee call.entered)) dst ↔
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.limeConfig call s outer out :=
  Resume.Proofs.entered_run_iff checked continuation (cont.limeConfig call s outer) _
    (fun h live => callee_step checked allocated h live)
    (fun ready entered => Graph.lime_entered_frame_step_iff checked.graph allocated continuation.found rfl ready entered)
    (handoff continuation)

theorem run_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (tableFound : frameTable s call.caller = some call.site.table) {dst : Config H} :
    Steps CallFrame.limeNoHost
      (cont.limeSiteWrap outer (limeSource s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.limeEmit))) dst ↔
      dst ∈ (cont.limePrefix call s outer).dropLast ∨
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.limeConfig call s outer out := by
  have exactPrefix := prefix_exact (cont := cont) (outer := outer) checked allocated tableFound
  have path := prefix_run_iff (dst := dst) (native := Step CallFrame.limeNoHost)
    (cont.limePrefix call s outer).dropLast (cont.limeConfig call s outer (.callee call.entered)) (by exact exactPrefix)
  exact path.trans (or_congr Iff.rfl (entered_run_iff checked allocated.links continuation))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs.Lime1
