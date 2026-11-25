module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {H : Type} {s : Store H} {entry : Entry} {program : Graph.Program} {tables : Source.Tables}
  {outer : Frame} {index : FuncIdx} {args : List Value} {active : Source.Activation}

private theorem tail_code (fn : Graph.Function) (tail : List Graph.Op) :
    expression (Graph.Op.emitList Graph.limeCodeSyntax tail) = tail.map Graph.limeEmit := by
  have code := Graph.lime_body_expression
    { fn with initial := [], code := tail }
  exact code

private theorem site_code (entry : Entry) :
    expression entry.siteBody.lime = entry.limeSiteCode entry.before := by
  change expression
    (entry.before.map (fun op => Graph.Op.emit Graph.limeCodeSyntax (.numeric op)) ++
      entry.op.limeInstr :: Graph.Op.emitList Graph.limeCodeSyntax entry.cont.code) = _
  simp only [expression, List.map_append, List.map_cons, List.map_map]
  change _ ++ .source entry.op.limeInstr :: expression (Graph.Op.emitList Graph.limeCodeSyntax entry.cont.code) = _
  rw [tail_code entry.cont.owner]
  unfold Entry.limeSiteCode
  congr 1
  apply List.map_congr_left
  intro op _
  cases op <;> rfl

private theorem body_code (entry : Entry) :
    expression entry.limeFunc.body = values entry.cont.owner.initial ++ expression entry.body.lime := by
  have literals := Graph.lime_body_expression { entry.cont.owner with code := [] }
  change expression (entry.cont.owner.initial.map Graph.limeCodeSyntax.ops.value ++ []) =
    values entry.cont.owner.initial ++ [] at literals
  rw [List.append_nil, List.append_nil] at literals
  change expression (entry.cont.owner.initial.map Graph.limeCodeSyntax.ops.value ++ entry.body.lime) = _
  simp only [expression, List.map_append] at literals ⊢
  rw [literals]

private theorem function_site (scope : entry.cont.block = none) :
    entry.limeBody s outer args = entry.limeOperands s outer args (entry.initial, entry.before) := by
  simp [Entry.limeBody, body_code, Entry.body, scope, site_code, Entry.limeOperands, Entry.initial,
    Context.Resume.Continuation.limeSiteWrap, Context.Resume.Continuation.scopes, Context.limeNest]

private theorem block_iff {block : Context.Resume.Block}
    (scope : entry.cont.block = some block) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeBody s outer args) dst ↔
      dst = entry.limeOperands s outer args (entry.initial, entry.before) := by
  let body := entry.siteBody.lime
  let tail := block.tail.map Graph.limeEmit
  let blockCode := values entry.cont.owner.initial ++ .source (.block (Blocks.limeType block.result) body) :: tail
  have rendered : expression entry.limeFunc.body = blockCode := by
    rw [body_code, Entry.body, scope]
    change values entry.cont.owner.initial ++ .source (.block (Blocks.limeType block.result) body) ::
      expression (Graph.Op.emitList Graph.limeCodeSyntax block.tail) = blockCode
    rw [tail_code entry.cont.owner]
  have stays (out : List Admin) : ¬ PureStep (entry.frame args).module.types [.label entry.cont.owner.declaration.results.length []
      blockCode] out :=
    Computed.lime_label_stays (head := .source (.block (Blocks.limeType block.result) body))
      rfl (by simp) (by simp) (by simp)
  simp only [Entry.limeBody, rendered]
  rw [Context.Resume.lime_wrap_step_iff stays]
  have enter (mid : Config H) := Computed.lime_block_iff (s := s) (f := entry.frame args) (dst := mid)
    (result := block.result) (body := body) (rest := tail)
    (stack := entry.cont.owner.initial)
  change (∃ mid, Step CallFrame.limeNoHost ⟨s, entry.frame args, blockCode⟩ mid ∧ _) ↔ _
  simp only [blockCode, enter, exists_eq_left]
  rw [show expression body = entry.limeSiteCode entry.before from site_code entry]
  simp [Entry.limeOperands, Entry.initial, scope, tail,
    Context.Resume.Continuation.limeSiteWrap, Context.Resume.Continuation.scopes, Context.limeNest, values]

private theorem entry_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance) {dst : Config H} :
    Step CallFrame.limeNoHost (entry.limeInvoke s outer args) dst ↔
      dst = entry.limeBody s outer args := by
  have count : args.length = entry.cont.owner.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length ready.typed)
  have enter := CallFrame.lime_invoke_wasm_exact (caller := outer) (dst := dst) allocated count
  change Step CallFrame.limeNoHost (entry.limeInvoke s outer args) dst ↔
    dst = ⟨s, outer, [.frame entry.cont.owner.declaration.results.length (entry.cont.owner.declaration.frame args)
      [.label entry.cont.owner.declaration.results.length [] (expression entry.limeFunc.body)]]⟩ at enter
  exact enter

private theorem operand_iff {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {ans : Prefix.Outcome} (move : Prefix.Reduce (entry.frame args).locals stack op ans)
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeOperands s outer args (stack, op :: rest)) dst ↔
      dst = match ans with
      | .values next => entry.limeOperands s outer args (next, rest)
      | .trap saved => entry.limeOperandResult s outer args (.trap saved rest) := by
  let tail := entry.limeSiteCode rest
  let inside : Config H := ⟨s, entry.frame args, values stack ++ Prefix.emit limeSyntax op :: tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ PureStep (entry.frame args).module.types [.label n [] inside.code] out :=
    Computed.lime_label_stays (by cases op <;> rfl)
      (by cases op <;> simp [Prefix.emit, limeSyntax])
      (by cases op <;> simp [Prefix.emit, limeSyntax])
      (by cases op <;> simp [Prefix.emit, limeSyntax])
  have wrap (result : Prefix.Outcome) :
      entry.cont.limeSiteWrap outer ⟨s, entry.frame args, Prefix.outcomeCode values .trap tail result⟩ =
        match result with
        | .values next => entry.limeOperands s outer args (next, rest)
        | .trap saved => entry.limeOperandResult s outer args (.trap saved rest) := by
    cases result with
    | values => rfl
    | trap => cases scope : entry.cont.block <;>
        simp [Entry.limeOperandResult, Entry.limeCleanup, Entry.siteTrap, Context.Resume.Continuation.limeSiteWrap,
          Context.Resume.Continuation.scopes, Context.limeNest, Blocks.Context.Scope.plug, scope, Prefix.outcomeCode, tail]
  change Step CallFrame.limeNoHost (entry.cont.limeSiteWrap outer inside) dst ↔ _
  rw [Context.Resume.lime_site_step_iff stays]
  constructor
  · rintro ⟨mid, step, eq⟩
    obtain ⟨actual, reduced, rfl⟩ := (Prefix.lime_step_iff (tail := tail)).mp step
    cases Prefix.reduce_unique reduced move
    cases ans <;> exact eq.trans (wrap _)
  · intro eq
    have step := (Prefix.lime_step_iff (s := s) (f := entry.frame args) (tail := tail)).mpr ⟨ans, move, rfl⟩
    cases ans with
    | values next => exact ⟨_, step, eq.trans (wrap (.values next)).symm⟩
    | trap saved => exact ⟨_, step, eq.trans (wrap (.trap saved)).symm⟩

private theorem operand_chain {stack : List Value} {code : List Prefix.Op}
    {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace (entry.frame args).locals stack code states result) :
    (states.map (entry.limeOperands s outer args) ++ [entry.limeOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  induction trace with
  | done => exact .singleton _
  | value step next ih =>
    apply ih.cons
    have head := operand_head (entry.limeOperands s outer args) (entry.limeOperandResult s outer args)
      (fun _ => rfl) next
    intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact operand_iff step dst
  | trap step => exact List.isChain_pair.mpr (operand_iff step)

theorem operands_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    (entry.limeBefore s outer index args states ++ [entry.limeOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have head := operand_head (entry.limeOperands s outer args) (entry.limeOperandResult s outer args)
    (fun _ => rfl) trace
  have call : ∀ dst, Step CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst = entry.limeInvoke s outer args := fun _ =>
    Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) ready.resolves
  have after := operand_chain (s := s) (outer := outer) trace
  unfold Entry.limeBefore
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
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.limePrefix s outer index args active out states).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have prepare := prepare_spec ready
  have data := prepare.checked
  have before := operands_exact ready.checked allocated.entry ready.trace
  let site := entry.cont.limeWrap outer (active.limeSource s entry.cont.scopes entry.cont.code)
  have lookup : [site, entry.cont.limeWrap outer (active.limeResolved s entry.cont.scopes entry.cont.code out)].IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    List.isChain_pair.mpr (fun _ => Context.Resume.lime_resolution_allocated_iff data.site allocated.targets
      (Source.lime_table data allocated.tables) resolved)
  have same : entry.limeOperandResult s outer args (.values stack) = site := by
    simp only [Entry.limeOperandResult, Entry.limeOperands, Entry.limeSiteCode, site,
      Source.Activation.limeSource, Context.Resume.Continuation.limeSiteWrap, Source.limeNest, Indirect.limeSource,
      prepare.caller_eq, Entry.frame, prepare.stack_eq, List.map_nil, List.nil_append,
      Source.Op.limeInstr, ← prepare.typeIndex_eq, values,
      List.append_assoc, Value.int]
  rw [same] at before
  simpa only [Entry.limePrefix, site, List.append_assoc, List.singleton_append] using
    List.IsChain.append_overlap before lookup (by simp)

theorem run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (GraphEntry.limeSource s outer index args) dst ↔
      dst ∈ entry.limePrefix s outer index args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.limeConfig call s outer phase := by
  obtain ⟨callChecked, continuation⟩ := resume_guard ready invoked
  obtain ⟨member, found, resolved⟩ := resolved_entry_ref invoked
  let before := entry.limePrefix s outer index args active (.resolved call.address) states
  let entered := entry.cont.limeConfig call s outer (.callee call.entered)
  have steps := prefix_exact ready allocated resolved
  have enter : ∀ dst, Step CallFrame.limeNoHost
      (entry.cont.limeWrap outer (active.limeResolved s entry.cont.scopes entry.cont.code (.resolved call.address))) dst ↔
      dst = entered := by
    obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
    exact fun _ => Context.Resume.lime_entry_iff callChecked (allocated.targets address callee member found)
  have chain : (before ++ [entered]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    steps.append (.singleton entered) (by
      intro a aLast b bFirst
      simp [Entry.limePrefix] at aLast
      change b ∈ some entered at bFirst
      subst a
      obtain rfl := Option.mem_some.mp bFirst
      exact enter)
  exact (Context.Resume.prefix_run_iff (dst := dst) before entered chain).trans
    (or_congr Iff.rfl (Context.Resume.lime_entered_run_iff callChecked allocated.links continuation))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Lime1
