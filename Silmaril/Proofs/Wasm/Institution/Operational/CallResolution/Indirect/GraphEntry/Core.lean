module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H}
  {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Runtime.Frame}
  {index : FuncIdx} {args : List Value} {active : Source.Activation}

private theorem tail_code (fn : Graph.Function) (tail : List Graph.Op) :
    expression (Graph.Op.emitList Graph.coreCodeSyntax tail) = tail.map Graph.coreEmit := by
  have code := Graph.core_body_expression
    { fn with initial := [], code := tail }
  exact code

private theorem site_code (entry : Entry) :
    expression entry.siteBody.core = entry.coreSiteCode entry.before := by
  change expression
    (entry.before.map (fun op => Graph.Op.emit Graph.coreCodeSyntax (.numeric op)) ++
      entry.op.coreInstr :: Graph.Op.emitList Graph.coreCodeSyntax entry.cont.code) = _
  simp only [expression, List.map_append, List.map_cons, List.map_map]
  change _ ++ .plain entry.op.coreInstr :: expression (Graph.Op.emitList Graph.coreCodeSyntax entry.cont.code) = _
  rw [tail_code entry.cont.owner]
  unfold Entry.coreSiteCode
  congr 1
  apply List.map_congr_left
  intro op _
  cases op <;> rfl

private theorem body_code (entry : Entry) :
    expression entry.coreFunc.body = coreValues entry.cont.owner.initial ++ expression entry.body.core := by
  have literals := Graph.core_body_expression { entry.cont.owner with code := [] }
  change expression (entry.cont.owner.initial.map Graph.coreCodeSyntax.ops.value ++ []) =
    coreValues entry.cont.owner.initial ++ [] at literals
  rw [List.append_nil, List.append_nil] at literals
  change expression (entry.cont.owner.initial.map Graph.coreCodeSyntax.ops.value ++ entry.body.core) = _
  simp only [expression, List.map_append] at literals ⊢
  rw [literals]

private theorem function_site (scope : entry.cont.block = none) :
    entry.coreBody s outer args = entry.coreOperands s outer args (entry.initial, entry.before) := by
  simp [Entry.coreBody, body_code, Entry.body, scope, site_code, Entry.coreOperands, Entry.initial,
    Context.Resume.Continuation.coreSiteWrap, Context.Resume.Continuation.scopes, Context.coreNest]

private theorem block_iff {block : Context.Resume.Block}
    (scope : entry.cont.block = some block) (dst : Config H) :
    Step P noHost (entry.coreBody s outer args) dst ↔
      dst = entry.coreOperands s outer args (entry.initial, entry.before) := by
  let body := entry.siteBody.core
  let tail := block.tail.map Graph.coreEmit
  let blockCode := coreValues entry.cont.owner.initial ++ .plain (.block (Blocks.coreType block.result) body) :: tail
  have rendered : expression entry.coreFunc.body = blockCode := by
    rw [body_code, Entry.body, scope]
    change coreValues entry.cont.owner.initial ++ .plain (.block (Blocks.coreType block.result) body) ::
      expression (Graph.Op.emitList Graph.coreCodeSyntax block.tail) = blockCode
    rw [tail_code entry.cont.owner]
  have stays (out : List Admin) : ¬ LabelExit entry.cont.owner.declaration.results.length []
      blockCode out :=
    Computed.core_label_stays (head := .plain (.block (Blocks.coreType block.result) body))
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  simp only [Entry.coreBody, rendered]
  rw [Context.Resume.core_wrap_step_iff stays]
  have enter (mid : Config H) := Blocks.core_context_entry_iff (P := P) (s := s) (f := (entry.frame args).toCore) (dst := mid)
    (result := block.result) (body := body) (rest := tail)
    (saved := entry.cont.owner.initial.map Value.toCore)
  change (∃ mid, Step P noHost ⟨s, (entry.frame args).toCore, blockCode⟩ mid ∧ _) ↔ _
  simp only [blockCode, enter, exists_eq_left]
  rw [show expression body = entry.coreSiteCode entry.before from site_code entry]
  simp [Entry.coreOperands, Entry.initial, scope, tail,
    Context.Resume.Continuation.coreSiteWrap, Context.Resume.Continuation.scopes, Context.coreNest, coreValues]

private theorem entry_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance) {dst : Config H} :
    Step P noHost (entry.coreInvoke s outer args) dst ↔ dst = entry.coreBody s outer args := by
  have enter := Sequence.wasm_entry_iff (P := P) (caller := outer) (dst := dst) allocated ready.typed
  have frame := Sequence.core_frame_forCall entry.cont.owner.declaration.module args entry.cont.owner.declaration.locals
  change Core.Frame.forCall entry.cont.owner.declaration.module.toCore (args.map Value.toCore) entry.coreFunc.locals =
    (entry.cont.owner.declaration.frame args).toCore at frame
  rw [frame] at enter
  exact enter

private theorem operand_iff {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {ans : Prefix.Outcome} (move : Prefix.Reduce (entry.frame args).locals stack op ans)
    (dst : Config H) :
    Step P noHost (entry.coreOperands s outer args (stack, op :: rest)) dst ↔
      dst = match ans with
      | .values next => entry.coreOperands s outer args (next, rest)
      | .trap saved => entry.coreOperandResult s outer args (.trap saved rest) := by
  let tail := entry.coreSiteCode rest
  let inside : Config H := ⟨s, (entry.frame args).toCore, coreValues stack ++ Prefix.emit coreSyntax op :: tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ LabelExit n [] inside.code out :=
    Computed.core_label_stays (by cases op <;> rfl)
      (by cases op <;> simp [Prefix.emit, coreSyntax])
      (by cases op <;> simp [Prefix.emit, coreSyntax])
      (by cases op <;> simp [Prefix.emit, coreSyntax, Admin.IsReturnCallRef])
      (by cases op <;> simp [Prefix.emit, coreSyntax]) (by cases op <;> simp [Prefix.emit, coreSyntax])
  have wrap (result : Prefix.Outcome) :
      entry.cont.coreSiteWrap outer ⟨s, (entry.frame args).toCore, Prefix.outcomeCode coreValues .trap tail result⟩ =
        match result with
        | .values next => entry.coreOperands s outer args (next, rest)
        | .trap saved => entry.coreOperandResult s outer args (.trap saved rest) := by
    cases result with
    | values => rfl
    | trap => cases scope : entry.cont.block <;>
        simp [Entry.coreOperandResult, Entry.coreCleanup, Entry.siteTrap, Context.Resume.Continuation.coreSiteWrap,
          Context.Resume.Continuation.scopes, Context.coreNest, Blocks.Context.Scope.plug, scope, Prefix.outcomeCode, tail]
  change Step P noHost (entry.cont.coreSiteWrap outer inside) dst ↔ _
  rw [Context.Resume.core_site_step_iff stays]
  constructor
  · rintro ⟨mid, step, eq⟩
    obtain ⟨actual, reduced, rfl⟩ := (Prefix.core_step_iff (P := P) (tail := tail)).mp step
    cases Prefix.reduce_unique reduced move
    cases ans <;> exact eq.trans (wrap _)
  · intro eq
    have step := (Prefix.core_step_iff (P := P) (s := s) (f := entry.frame args) (tail := tail)).mpr ⟨ans, move, rfl⟩
    cases ans with
    | values next => exact ⟨_, step, eq.trans (wrap (.values next)).symm⟩
    | trap saved => exact ⟨_, step, eq.trans (wrap (.trap saved)).symm⟩

private theorem operand_chain {stack : List Value} {code : List Prefix.Op}
    {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace (entry.frame args).locals stack code states result) :
    (states.map (entry.coreOperands s outer args) ++ [entry.coreOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  induction trace with
  | done => exact .singleton _
  | value step next ih =>
    apply ih.cons
    have head := operand_head (entry.coreOperands s outer args) (entry.coreOperandResult s outer args)
      (fun _ => rfl) next
    intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact operand_iff step dst
  | trap step => exact List.isChain_pair.mpr (operand_iff step)

theorem operands_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    (entry.coreBefore s outer index args states ++ [entry.coreOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have head := operand_head (entry.coreOperands s outer args) (entry.coreOperandResult s outer args)
    (fun _ => rfl) trace
  have call : ∀ dst, Step P noHost (coreSource s outer index args) dst ↔
      dst = entry.coreInvoke s outer args := fun _ =>
    Computed.core_direct_call_iff (s := s) (P := P) (stack := args) (tail := []) ready.resolves allocated
  have after := operand_chain (s := s) (outer := outer) (P := P) trace
  unfold Entry.coreBefore
  cases scope : entry.cont.block with
  | none =>
    refine List.isChain_cons_cons.mpr ⟨call, after.cons ?_⟩
    intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    rw [← function_site scope]
    exact entry_iff ready allocated
  | some block =>
    refine List.isChain_cons_cons.mpr ⟨call, List.isChain_cons_cons.mpr
      ⟨fun _ => entry_iff ready allocated, after.cons ?_⟩⟩
    intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact block_iff scope dst

theorem prefix_exact {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.corePrefix s outer index args active out states).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have prepare := prepare_spec ready
  have data := prepare.checked
  have before := operands_exact (P := P) ready.checked allocated.entry ready.trace
  have lookup := Context.Resume.core_resolution_allocated_exact (P := P) (cont := entry.cont) (outer := outer)
    (stack := active.operands.saved ++ active.operands.args) data.site allocated.targets
    (Source.core_table data allocated.tables) resolved
  have chain := (List.isChain_map (R := fun a b : Config H => ∀ dst, Step P noHost a dst ↔ dst = b)
    (entry.coreLookup s outer active)).mpr lookup
  have same : entry.coreOperandResult s outer args (.values stack) = entry.coreLookup s outer active .start := by
    have selector : vals [(Value.int .i32 active.operands.selector).toCore] =
        [constI32 active.operands.selector] := rfl
    simp only [Entry.coreOperandResult, Entry.coreOperands, Entry.coreSiteCode, Entry.coreLookup,
      Source.Activation.coreConfig, Context.Resume.Continuation.coreSiteWrap, Source.coreNest, Indirect.coreConfig, Site.coreCode,
      prepare.caller_eq, Entry.frame, prepare.stack_eq, List.map_nil, List.nil_append,
      coreValues, Source.Op.coreInstr, ← prepare.typeIndex_eq, List.map_append, List.map_singleton,
      vals_append, selector, List.append_assoc, List.cons_append]
  rw [same] at before
  have traceHead : out.coreTrace = .start :: out.coreTrace.tail := by cases out <;> rfl
  have lookupChain : ([entry.coreLookup s outer active .start] ++
      out.coreTrace.tail.map (entry.coreLookup s outer active)).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
    rw [List.cons_append, List.nil_append, ← List.map_cons, ← traceHead]
    exact chain
  rw [Entry.corePrefix, traceHead, List.map_cons]
  rw [show entry.coreLookup s outer active .start :: List.map (entry.coreLookup s outer active)
    out.coreTrace.tail = [entry.coreLookup s outer active .start] ++
      out.coreTrace.tail.map (entry.coreLookup s outer active) from rfl, ← List.append_assoc]
  exact before.append_overlap lookupChain (by simp)


theorem run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ entry.corePrefix s outer index args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.coreConfig call s outer phase := by
  obtain ⟨callChecked, continuation⟩ := resume_guard ready invoked
  obtain ⟨member, found, resolved⟩ := resolved_entry_ref invoked
  let before := entry.corePrefix s outer index args active (.resolved call.address) states
  let entered := entry.cont.coreConfig call s outer (.callee call.entered)
  have steps := prefix_exact (P := P) ready allocated resolved
  have enter : ∀ dst, Step P noHost (entry.coreLookup s outer active (.call (some call.address))) dst ↔
      dst = entered := by
    obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
    exact fun _ => Context.Resume.core_entry_iff callChecked (allocated.targets address callee member found)
  have chain : (before ++ [entered]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
    steps.append (.singleton entered) (by
      intro a aLast b bFirst
      simp [Entry.corePrefix, Outcome.coreTrace] at aLast
      change b ∈ some entered at bFirst
      subst a
      obtain rfl := Option.mem_some.mp bFirst
      exact enter)
  exact (Context.Resume.prefix_run_iff (dst := dst) before entered chain).trans
    (or_congr Iff.rfl (Context.Resume.core_entered_run_iff callChecked allocated.links continuation))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Core
