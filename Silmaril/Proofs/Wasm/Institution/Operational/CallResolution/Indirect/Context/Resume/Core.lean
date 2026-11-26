module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Core
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
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

theorem core_wrap_step_iff {inner dst : Config H}
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

theorem core_site_step_iff {inner dst : Config H}
    (stays : ∀ n out, ¬ LabelExit n [] inner.code out) :
    Step P noHost (cont.coreSiteWrap outer inner) dst ↔
      ∃ mid, Step P noHost inner mid ∧ dst = cont.coreSiteWrap outer mid := by
  have nest := Source.core_nest_step (P := P) stays cont.scopes
  rw [Continuation.coreSiteWrap, core_wrap_step_iff (fun out => nest.1 _ out)]
  constructor
  · rintro ⟨nested, move, rfl⟩
    obtain ⟨mid, step, rfl⟩ := (nest.2 nested).mp move
    exact ⟨mid, step, rfl⟩
  · rintro ⟨mid, step, rfl⟩
    exact ⟨_, (nest.2 _).mpr ⟨mid, step, rfl⟩, rfl⟩

private theorem site_exact {a b : Config H}
    (stays : ∀ n out, ¬ LabelExit n [] a.code out)
    (step : ∀ dst, Step P noHost a dst ↔ dst = b) :
    ∀ dst, Step P noHost (cont.coreSiteWrap outer a) dst ↔ dst = cont.coreSiteWrap outer b := by
  intro dst
  rw [core_site_step_iff stays]
  simp only [step, exists_eq_left]

theorem resolution_prefix_exact {site : Indirect.Site} {caller : Runtime.Frame} {out : Outcome}
    {selector : BitVec 32} {stack : List Value} {addr : Nat}
    (checked : site.check program caller = true) (allocated : site.CoreAllocated program s)
    (tableFound : s.table? caller.toCore tableIndex = some (addr, site.table.toCore))
    (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Step P noHost (cont.coreSiteWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) a)) dst ↔
        dst = cont.coreSiteWrap outer (Indirect.coreConfig s caller site selector stack (cont.code.map Graph.coreEmit) b)) := by
  have chain := Indirect.core_trace_allocated_exact (P := P) (stack := stack) (rest := cont.code.map Graph.coreEmit)
    checked allocated tableFound resolved
  have live (a : Indirect.Phase) (mem : a ∈ (out.coreTrace).dropLast) : a.Pending := by
    cases out <;>
      simp only [Outcome.coreTrace, List.cons_append, List.nil_append, List.dropLast_cons_cons, List.dropLast_singleton,
        List.mem_cons, List.not_mem_nil, or_false] at mem <;>
      rcases mem with rfl | rfl | rfl | rfl <;> trivial
  let render a := cont.coreSiteWrap outer (Indirect.coreConfig s caller site selector stack
    (cont.code.map Graph.coreEmit) a)
  apply (List.isChain_map (R := fun a b : Config H => ∀ dst, Step P noHost a dst ↔ dst = b) render).mp
  exact map_chain render chain (fun a mem b exactStep => site_exact (cont := cont) (outer := outer)
    (Indirect.core_lookup_stays (live a mem)) exactStep)

theorem prefix_exact (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) :
    (cont.corePrefix call s outer).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  let inner := Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
    (cont.code.map Graph.coreEmit)
  refine map_chain (cont.coreSiteWrap outer) (Context.core_prefix_exact (P := P) checked allocated tableFound) ?_
  intro a mem b exactStep
  change a ∈ [inner .start, inner .lookup, inner (.cast (some call.address)), inner (.call (some call.address))] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · exact site_exact (Indirect.core_lookup_stays (phase := .start) trivial) exactStep
  · exact site_exact (Indirect.core_lookup_stays (phase := .lookup) trivial) exactStep
  · exact site_exact (Indirect.core_lookup_stays (phase := .cast (some call.address)) trivial) exactStep
  · exact site_exact (Indirect.core_lookup_stays (phase := .call (some call.address)) trivial) exactStep

theorem entry_iff (checked : call.Checked program)
    (allocated : s.funcs[call.address.value]? = some call.callee.coreInstance) {dst : Config H} :
    Step P noHost (cont.coreSiteWrap outer (Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.coreEmit) (.call (some call.address)))) dst ↔
      dst = cont.coreConfig call s outer (.callee call.entered) := by
  have entry := site_exact (cont := cont) (outer := outer) (Indirect.core_lookup_stays (phase := .call (some call.address)) trivial)
    (fun _ => Indirect.core_enter_at_iff (P := P) (caller := call.caller) (saved := call.saved)
      (rest := cont.code.map Graph.coreEmit) allocated checked.found checked.resolved checked.typed) dst
  exact entry.trans (by rw [Context.Proofs.Core.entered_config]; rfl)

theorem plug_code (blocks : List Block) (saved : List Value) (body : Graph.Body)
    (cfg : Config H) (code : cfg.code = body.render Graph.coreAdmin) :
    (Context.coreNest (Block.scopes blocks saved) cfg).code =
      (Block.plug blocks saved body).render Graph.coreAdmin := by
  induction blocks generalizing saved with
  | nil => exact code
  | cons block rest ih =>
    exact congrArg (fun code => coreValues saved ++
      .label block.result.toList.length [] code :: block.tail.map Graph.coreEmit) (ih [])


private theorem handoff (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (result : Nested.Result) :
    cont.coreConfig call s outer (.callee (.done result)) =
      cont.coreConfig call s outer (.caller (cont.resume call.caller call.saved result)) := by
  let returned := call.coreCallee s (cont.code.map Graph.coreEmit) (.done result)
  have code : returned.code = (cont.deliver call.saved result).render Graph.coreAdmin := by
    cases result <;> simp [returned, Invocation.coreCallee, Continuation.deliver,
      Graph.Phase.render, Graph.Phase.renderAt, Graph.coreAdmin, Graph.Body.render,
      Nested.resultCode, coreValues, vals_append, List.map_append, List.append_assoc]
  have source := plug_code cont.blocks cont.owner.initial (cont.deliver call.saved result) returned code
  have same (scopes : List (Blocks.Context.Scope Graph.Op)) :
      (Context.coreNest scopes returned).store = s ∧
      (Context.coreNest scopes returned).frame = call.caller.toCore := by
    induction scopes with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ ih => exact ih
  obtain ⟨store, frame⟩ := same cont.scopes
  change cont.coreWrap outer (Context.coreNest cont.scopes returned) = _
  unfold Continuation.coreWrap
  rw [store, frame]
  change (Context.coreNest cont.scopes returned).code = _ at source
  rw [source]
  simp only [Continuation.coreConfig, Continuation.resume, Continuation.plug, Continuation.target,
    Graph.coreConfig, Graph.Phase.render, Graph.Phase.renderAt, Graph.coreAdmin,
    Graph.LabelKind.arity, Graph.LabelKind.cont, Graph.currentFrame]
  rw [← continuation.module_eq]

private theorem callee_step (checked : call.Checked program) (allocated : program.CoreLinksAllocated s)
    {a : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step P noHost (cont.coreConfig call s outer (.callee a)) dst ↔
      ∃ out, program.FrameEdge call.address a out ∧ dst = cont.coreConfig call s outer (.callee out) := by
  obtain ⟨n, f, body, render⟩ := Context.Proofs.Core.frame_shape (call := call) live
  have stays (nlabel : Nat) (out : List Admin) :
      ¬ LabelExit nlabel []
        (call.coreCallee s (cont.code.map Graph.coreEmit) a).code out := by
    simp only [Invocation.coreCallee, render, List.append_assoc, List.singleton_append]
    exact Computed.core_label_stays (head := .frame n f body) rfl (by simp) (by simp)
      (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (cont.coreSiteWrap outer (call.coreCallee s (cont.code.map Graph.coreEmit) a)) dst ↔ _
  rw [core_site_step_iff stays]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨out, move, rfl⟩ := (Context.Proofs.Core.linked_frame_step_iff checked allocated ready live).mp step
    exact ⟨out, move, rfl⟩
  · rintro ⟨out, move, rfl⟩
    exact ⟨_, (Context.Proofs.Core.linked_frame_step_iff checked allocated ready live).mpr ⟨_, move, rfl⟩, rfl⟩

theorem entered_run_iff (checked : call.Checked program) (allocated : program.CoreLinksAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {dst : Config H} :
    Steps P noHost (cont.coreConfig call s outer (.callee call.entered)) dst ↔
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.coreConfig call s outer out :=
  Resume.Proofs.entered_run_iff checked continuation (cont.coreConfig call s outer) _
    (fun h live => callee_step checked allocated h live)
    (fun ready entered => Graph.core_entered_frame_step_iff checked.graph allocated continuation.found rfl ready entered)
    (handoff continuation)

theorem run_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore))
    {dst : Config H} :
    Steps P noHost
      (cont.coreSiteWrap outer (Indirect.coreConfig s call.caller call.site call.selector (call.saved ++ call.args)
        (cont.code.map Graph.coreEmit) .start)) dst ↔
      dst ∈ (cont.corePrefix call s outer).dropLast ∨
      ∃ out, Runs program call cont (.callee call.entered) out ∧ dst = cont.coreConfig call s outer out := by
  have exactPrefix := prefix_exact (P := P) (cont := cont) (outer := outer) checked allocated tableFound
  have path := prefix_run_iff (dst := dst) (native := Step P noHost)
    (cont.corePrefix call s outer).dropLast (cont.coreConfig call s outer (.callee call.entered)) (by exact exactPrefix)
  exact path.trans (or_congr Iff.rfl (entered_run_iff checked allocated.links continuation))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs.Core
