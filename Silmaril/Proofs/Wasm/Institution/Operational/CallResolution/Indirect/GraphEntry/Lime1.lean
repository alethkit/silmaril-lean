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

theorem site_code (entry : Entry) :
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

private theorem block_iff (entered : List (Blocks.Context.Scope Graph.Op)) (saved : List Value)
    (block : Context.Resume.Block) (rest : List Context.Resume.Block) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeRegion s outer args entered saved (block :: rest)) dst ↔
      dst = entry.limeRegion s outer args (entered ++ [block.scope saved]) [] rest := by
  let body := (entry.region rest).lime
  let tail := block.tail.map Graph.limeEmit
  let code := values saved ++ .source (.block (Blocks.limeType block.result) body) :: tail
  have rendered : values saved ++ expression (entry.region (block :: rest)).lime = code := by
    change values saved ++ .source (.block (Blocks.limeType block.result) body) ::
      expression (Graph.Op.emitList Graph.limeCodeSyntax block.tail) = code
    rw [tail_code entry.cont.owner]
  have stays (n : Nat) (out : List Admin) : ¬ PureStep (entry.frame args).module.types [.label n [] code] out :=
    Computed.lime_label_stays (head := .source (.block (Blocks.limeType block.result) body))
      rfl (by simp) (by simp) (by simp)
  have nest := Source.lime_nest_step (a := ⟨s, entry.frame args, code⟩) stays entered
  simp only [Entry.limeRegion, rendered]
  rw [Context.Resume.lime_wrap_step_iff (fun out => nest.1 _ out)]
  have enter (mid : Config H) := Computed.lime_block_iff (s := s) (f := entry.frame args) (dst := mid)
    (result := block.result) (body := body) (rest := tail) (stack := saved)
  let target : Config H := ⟨s, entry.frame args, values saved ++
    .label block.result.toList.length [] (expression body) :: tail⟩
  have same : Context.limeNest entered target =
      Context.limeNest (entered ++ [block.scope saved]) ⟨s, entry.frame args, values [] ++ expression body⟩ := by
    simp [Context.limeNestWith, List.foldr_append, target, Context.Resume.Block.scope, tail, values]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨next, inside, rfl⟩ := (nest.2 mid).mp move
    have eq : next = target := enter next |>.mp inside
    rw [eq]
    exact congrArg (entry.cont.limeWrap outer) same
  · rintro rfl
    rw [← same]
    exact ⟨_, (nest.2 _).mpr ⟨target, (enter target).mpr rfl, rfl⟩, rfl⟩

private theorem block_chain (blocks : List Context.Resume.Block) (saved : List Value)
    (entered : List (Blocks.Context.Scope Graph.Op)) (after : List (Config H))
    (chain : after.IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b))
    (head : after.head? = some (entry.limeRegion s outer args (entered ++ Context.Resume.Block.scopes blocks saved)
      (if blocks.isEmpty then saved else []) [])) :
    let before := entry.limeBlocks s outer args entered saved blocks ++ after
    before.IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) ∧
      before.head? = some (entry.limeRegion s outer args entered saved blocks) := by
  induction blocks generalizing saved entered with
  | nil => exact ⟨chain, by simpa [Context.Resume.Block.scopes, Entry.limeBlocks] using head⟩
  | cons block rest ih =>
    have next := ih [] (entered ++ [block.scope saved])
      (by simpa [Context.Resume.Block.scopes, List.append_assoc] using head)
    refine ⟨next.1.cons ?_, rfl⟩
    intro b found dst
    rw [next.2] at found
    obtain rfl := Option.mem_some.mp found
    exact block_iff entered saved block rest dst

theorem lime_site_trap (inner : Execution.Runtime.Frame) (stack : List Value) (rest : List Admin) :
    entry.limeCleanup s outer inner (entry.siteTrap Graph.limeEmit stack rest) =
      entry.cont.limeSiteWrap outer ⟨s, inner, values stack ++ .trap :: rest⟩ := by
  simp [Entry.limeCleanup, Entry.siteTrap, Context.Resume.Continuation.limeSiteWrap,
    Context.limeNestWith, List.foldr_map]

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
    | trap saved => exact (lime_site_trap (entry.frame args) saved tail).symm
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

theorem ordinary_path (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance) :
    [limeSource s outer index args, entry.limeInvoke s outer args, entry.limeBody s outer args].IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_pair.mpr (fun _ => entry_iff ready allocated)⟩
  intro dst
  exact Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) ready.resolves

theorem operands_via (entrance : Entrance) (front : List (Config H))
    (enters : (front ++ [entry.limeEntrance s outer args entrance]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b))
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    ((front ++ entry.limeInside s outer args states entrance) ++ [entry.limeOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have head := operand_head (entry.limeOperands s outer args) (entry.limeOperandResult s outer args)
    (fun _ => rfl) trace
  have after := operand_chain (s := s) (outer := outer) trace
  have path : let suffix := entry.limeInside s outer args states entrance ++ [entry.limeOperandResult s outer args result]
      suffix.IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) ∧
        suffix.head? = some (entry.limeEntrance s outer args entrance) := by
    cases entrance with
    | operands => exact ⟨after, head⟩
    | body =>
      have site : entry.limeRegion s outer args entry.cont.scopes entry.initial [] =
          entry.limeOperands s outer args (entry.initial, entry.before) := by
        simp only [Entry.limeRegion, Entry.region, site_code, Entry.limeOperands, Context.Resume.Continuation.limeSiteWrap]
      rw [← site] at head
      have path := block_chain (entry := entry) (s := s) (outer := outer) (args := args) entry.cont.blocks entry.cont.owner.initial []
        _ after (by simpa only [List.nil_append, Context.Resume.Continuation.scopes, Entry.initial] using head)
      have same : entry.limeEntrance s outer args .body =
          entry.limeRegion s outer args [] entry.cont.owner.initial entry.cont.blocks := by
        simp [Entry.limeEntrance, Entry.limeBody, body_code, Entry.body, Entry.limeRegion, Context.limeNestWith]
      have first := path.2.trans (congrArg some same.symm)
      simpa only [Entry.limeInside, List.append_assoc] using And.intro path.1 first
  dsimp only at path
  generalize restEq : entry.limeInside s outer args states entrance ++
    [entry.limeOperandResult s outer args result] = suffix at path
  cases suffix with
  | nil => simp at path
  | cons first rest =>
    have eq : first = entry.limeEntrance s outer args entrance := Option.some.inj path.2
    subst first
    have merged := List.IsChain.append_overlap enters (l₃ := rest) path.1 (by simp)
    simpa only [List.append_assoc, ← restEq, List.singleton_append] using merged

theorem operands_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    (entry.limeBefore s outer index args states ++ [entry.limeOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  operands_via .body [limeSource s outer index args, entry.limeInvoke s outer args] (ordinary_path ready allocated) trace

theorem prefix_via {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (entrance : Entrance) (front : List (Config H))
    (enters : (front ++ [entry.limeEntrance s outer args entrance]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b))
    (tablesFound : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (front ++ entry.limeSitePath s outer args active out states entrance).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have prepare := prepare_spec ready
  have data := prepare.checked
  have before := operands_via entrance front enters ready.trace
  let site := entry.cont.limeWrap outer (active.limeSource s entry.cont.scopes entry.cont.code)
  have lookup : [site, entry.cont.limeWrap outer (active.limeResolved s entry.cont.scopes entry.cont.code out)].IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    List.isChain_pair.mpr (fun _ => Context.Resume.lime_resolution_allocated_iff data.site targets
      (Source.lime_table data tablesFound) resolved)
  have same : entry.limeOperandResult s outer args (.values stack) = site := by
    simp only [Entry.limeOperandResult, Entry.limeOperands, Entry.limeSiteCode, site,
      Source.Activation.limeSource, Context.Resume.Continuation.limeSiteWrap, Source.limeNest, Indirect.limeSource,
      prepare.caller_eq, Entry.frame, prepare.stack_eq, List.map_nil, List.nil_append,
      Source.Op.limeInstr, ← prepare.typeIndex_eq, values,
      List.append_assoc, Value.int]
  rw [same] at before
  simpa only [Entry.limeSitePath, site, List.append_assoc, List.singleton_append] using
    List.IsChain.append_overlap before lookup (by simp)

theorem prefix_exact {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.limePrefix s outer index args active out states).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  prefix_via ready .body [limeSource s outer index args, entry.limeInvoke s outer args]
    (ordinary_path ready.checked allocated.entry) allocated.tables allocated.targets resolved

theorem run_via {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (entrance : Entrance) (start : Config H) (front : List (Config H))
    (enters : (start :: front ++ [entry.limeEntrance s outer args entrance]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b))
    (tablesFound : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost start dst ↔
      dst ∈ (start :: front) ++ entry.limeSitePath s outer args active (.resolved call.address) states entrance ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.limeConfig call s outer phase := by
  obtain ⟨callChecked, continuation⟩ := resume_guard ready invoked
  obtain ⟨member, found, resolved⟩ := resolved_entry_ref invoked
  let before := (start :: front) ++ entry.limeSitePath s outer args active (.resolved call.address) states entrance
  let entered := entry.cont.limeConfig call s outer (.callee call.entered)
  have steps := prefix_via ready entrance (start :: front) enters tablesFound targets resolved
  have enter : ∀ dst, Step CallFrame.limeNoHost
      (entry.cont.limeWrap outer (active.limeResolved s entry.cont.scopes entry.cont.code (.resolved call.address))) dst ↔
      dst = entered := by
    obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
    exact fun _ => Context.Resume.lime_entry_iff callChecked (targets address callee member found)
  have chain : (before ++ [entered]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    steps.append (.singleton entered) (by
      intro a aLast b bFirst
      simp [List.getLast?_cons, Entry.limeSitePath] at aLast
      change b ∈ some entered at bFirst
      subst a
      obtain rfl := Option.mem_some.mp bFirst
      exact enter)
  exact (Context.Resume.prefix_run_iff (dst := dst) before entered chain).trans
    (or_congr Iff.rfl (Context.Resume.lime_entered_run_iff callChecked links continuation))

theorem run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (GraphEntry.limeSource s outer index args) dst ↔
      dst ∈ entry.limePrefix s outer index args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.limeConfig call s outer phase :=
  run_via ready .body (limeSource s outer index args) [entry.limeInvoke s outer args]
    (ordinary_path ready.checked allocated.entry) allocated.tables allocated.targets allocated.links invoked

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Lime1
