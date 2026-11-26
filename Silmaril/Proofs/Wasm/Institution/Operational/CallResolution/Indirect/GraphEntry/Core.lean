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

theorem site_code (entry : Entry) :
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

private theorem block_iff (entered : List (Blocks.Context.Scope Graph.Op)) (saved : List Value)
    (block : Context.Resume.Block) (rest : List Context.Resume.Block) (dst : Config H) :
    Step P noHost (entry.coreRegion s outer args entered saved (block :: rest)) dst ↔
      dst = entry.coreRegion s outer args (entered ++ [block.scope saved]) [] rest := by
  let body := (entry.region rest).core
  let tail := block.tail.map Graph.coreEmit
  let code := coreValues saved ++ .plain (.block (Blocks.coreType block.result) body) :: tail
  have rendered : coreValues saved ++ expression (entry.region (block :: rest)).core = code := by
    change coreValues saved ++ .plain (.block (Blocks.coreType block.result) body) ::
      expression (Graph.Op.emitList Graph.coreCodeSyntax block.tail) = code
    rw [tail_code entry.cont.owner]
  have stays (n : Nat) (out : List Admin) : ¬ LabelExit n [] code out :=
    Computed.core_label_stays (head := .plain (.block (Blocks.coreType block.result) body))
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  have nest := Source.core_nest_step (P := P) (a := ⟨s, (entry.frame args).toCore, code⟩) stays entered
  simp only [Entry.coreRegion, rendered]
  rw [Context.Resume.core_wrap_step_iff (fun out => nest.1 _ out)]
  have enter (mid : Config H) := Blocks.core_context_entry_iff (P := P) (s := s) (f := (entry.frame args).toCore) (dst := mid)
    (result := block.result) (body := body) (rest := tail) (saved := saved.map Value.toCore)
  let target : Config H := ⟨s, (entry.frame args).toCore, coreValues saved ++
    .label block.result.toList.length [] (expression body) :: tail⟩
  have same : Context.coreNest entered target =
      Context.coreNest (entered ++ [block.scope saved]) ⟨s, (entry.frame args).toCore, coreValues [] ++ expression body⟩ := by
    simp [Context.coreNestWith, List.foldr_append, target, Context.Resume.Block.scope, tail, coreValues]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨next, inside, rfl⟩ := (nest.2 mid).mp move
    have eq : next = target := enter next |>.mp inside
    rw [eq]
    exact congrArg (entry.cont.coreWrap outer) same
  · rintro rfl
    rw [← same]
    exact ⟨_, (nest.2 _).mpr ⟨target, (enter target).mpr rfl, rfl⟩, rfl⟩

private theorem block_chain (blocks : List Context.Resume.Block) (saved : List Value)
    (entered : List (Blocks.Context.Scope Graph.Op)) (after : List (Config H))
    (chain : after.IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b))
    (head : after.head? = some (entry.coreRegion s outer args (entered ++ Context.Resume.Block.scopes blocks saved)
      (if blocks.isEmpty then saved else []) [])) :
    let before := entry.coreBlocks s outer args entered saved blocks ++ after
    before.IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) ∧
      before.head? = some (entry.coreRegion s outer args entered saved blocks) := by
  induction blocks generalizing saved entered with
  | nil => exact ⟨chain, by simpa [Context.Resume.Block.scopes, Entry.coreBlocks] using head⟩
  | cons block rest ih =>
    have next := ih [] (entered ++ [block.scope saved])
      (by simpa [Context.Resume.Block.scopes, List.append_assoc] using head)
    refine ⟨next.1.cons ?_, rfl⟩
    intro b found dst
    rw [next.2] at found
    obtain rfl := Option.mem_some.mp found
    exact block_iff entered saved block rest dst

theorem core_site_trap (inner : Execution.Runtime.Frame) (stack : List Value) (rest : List Admin) :
    entry.coreCleanup s outer inner (entry.siteTrap Graph.coreEmit stack rest) =
      entry.cont.coreSiteWrap outer ⟨s, inner.toCore, coreValues stack ++ .trap :: rest⟩ := by
  simp [Entry.coreCleanup, Entry.siteTrap, Context.Resume.Continuation.coreSiteWrap,
    Context.coreNestWith, List.foldr_map]

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
    | trap saved => exact (core_site_trap (entry.frame args) saved tail).symm
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

theorem ordinary_path (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance) :
    [coreSource s outer index args, entry.coreInvoke s outer args, entry.coreBody s outer args].IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_pair.mpr (fun _ => entry_iff ready allocated)⟩
  intro dst
  exact Computed.core_direct_call_iff (s := s) (P := P) (stack := args) (tail := []) ready.resolves allocated

theorem operands_via (entrance : Entrance) (front : List (Config H))
    (enters : (front ++ [entry.coreEntrance s outer args entrance]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b))
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    ((front ++ entry.coreInside s outer args states entrance) ++ [entry.coreOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have head := operand_head (entry.coreOperands s outer args) (entry.coreOperandResult s outer args)
    (fun _ => rfl) trace
  have after := operand_chain (s := s) (outer := outer) (P := P) trace
  have path : let suffix := entry.coreInside s outer args states entrance ++ [entry.coreOperandResult s outer args result]
      suffix.IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) ∧
        suffix.head? = some (entry.coreEntrance s outer args entrance) := by
    cases entrance with
    | operands => exact ⟨after, head⟩
    | body =>
      have site : entry.coreRegion s outer args entry.cont.scopes entry.initial [] =
          entry.coreOperands s outer args (entry.initial, entry.before) := by
        simp only [Entry.coreRegion, Entry.region, site_code, Entry.coreOperands, Context.Resume.Continuation.coreSiteWrap]
      rw [← site] at head
      have path := block_chain (entry := entry) (s := s) (outer := outer) (args := args) (P := P) entry.cont.blocks entry.cont.owner.initial []
        _ after (by simpa only [List.nil_append, Context.Resume.Continuation.scopes, Entry.initial] using head)
      have same : entry.coreEntrance s outer args .body =
          entry.coreRegion s outer args [] entry.cont.owner.initial entry.cont.blocks := by
        simp [Entry.coreEntrance, Entry.coreBody, body_code, Entry.body, Entry.coreRegion, Context.coreNestWith]
      have first := path.2.trans (congrArg some same.symm)
      simpa only [Entry.coreInside, List.append_assoc] using And.intro path.1 first
  dsimp only at path
  generalize restEq : entry.coreInside s outer args states entrance ++
    [entry.coreOperandResult s outer args result] = suffix at path
  cases suffix with
  | nil => simp at path
  | cons first rest =>
    have eq : first = entry.coreEntrance s outer args entrance := Option.some.inj path.2
    subst first
    have merged := List.IsChain.append_overlap enters (l₃ := rest) path.1 (by simp)
    simpa only [List.append_assoc, ← restEq, List.singleton_append] using merged

theorem operands_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states : List OperandState} {result : OperandResult}
    (trace : entry.OperandTrace args states result) :
    (entry.coreBefore s outer index args states ++ [entry.coreOperandResult s outer args result]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
  operands_via .body [coreSource s outer index args, entry.coreInvoke s outer args] (ordinary_path (P := P) ready allocated) trace

theorem prefix_via {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (entrance : Entrance) (front : List (Config H))
    (enters : (front ++ [entry.coreEntrance s outer args entrance]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b))
    (tablesFound : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (front ++ entry.coreSitePath s outer args active out states entrance).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have prepare := prepare_spec ready
  have data := prepare.checked
  have before := operands_via (P := P) entrance front enters ready.trace
  have lookup := Context.Resume.core_resolution_allocated_exact (P := P) (cont := entry.cont) (outer := outer)
    (stack := active.operands.saved ++ active.operands.args) data.site targets
    (Source.core_table data tablesFound) resolved
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
  rw [Entry.coreSitePath, ← List.append_assoc, traceHead, List.map_cons]
  rw [show entry.coreLookup s outer active .start :: List.map (entry.coreLookup s outer active)
    out.coreTrace.tail = [entry.coreLookup s outer active .start] ++
      out.coreTrace.tail.map (entry.coreLookup s outer active) from rfl, ← List.append_assoc]
  exact before.append_overlap lookupChain (by simp)


theorem prefix_exact {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.corePrefix s outer index args active out states).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
  prefix_via (P := P) ready .body [coreSource s outer index args, entry.coreInvoke s outer args]
    (ordinary_path (P := P) ready.checked allocated.entry) allocated.tables allocated.targets resolved

theorem run_via {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (entrance : Entrance) (start : Config H) (front : List (Config H))
    (enters : (start :: front ++ [entry.coreEntrance s outer args entrance]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b))
    (tablesFound : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps P noHost start dst ↔
      dst ∈ (start :: front) ++ entry.coreSitePath s outer args active (.resolved call.address) states entrance ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.coreConfig call s outer phase := by
  obtain ⟨callChecked, continuation⟩ := resume_guard ready invoked
  obtain ⟨member, found, resolved⟩ := resolved_entry_ref invoked
  let before := (start :: front) ++ entry.coreSitePath s outer args active (.resolved call.address) states entrance
  let entered := entry.cont.coreConfig call s outer (.callee call.entered)
  have steps := prefix_via (P := P) ready entrance (start :: front) enters tablesFound targets resolved
  have enter : ∀ dst, Step P noHost (entry.coreLookup s outer active (.call (some call.address))) dst ↔
      dst = entered := by
    obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
    exact fun _ => Context.Resume.core_entry_iff callChecked (targets address callee member found)
  have chain : (before ++ [entered]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
    steps.append (.singleton entered) (by
      intro a aLast b bFirst
      simp [List.getLast?_cons, Entry.coreSitePath, Outcome.coreTrace] at aLast
      change b ∈ some entered at bFirst
      subst a
      obtain rfl := Option.mem_some.mp bFirst
      exact enter)
  exact (Context.Resume.prefix_run_iff (dst := dst) before entered chain).trans
    (or_congr Iff.rfl (Context.Resume.core_entered_run_iff callChecked links continuation))

theorem run_iff {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.CoreAllocated program tables active s)
    {call : Context.Invocation} (invoked : active.invocation program = some call) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ entry.corePrefix s outer index args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.cont (.callee call.entered) phase ∧
        dst = entry.cont.coreConfig call s outer phase :=
  run_via (P := P) ready .body (coreSource s outer index args) [entry.coreInvoke s outer args]
    (ordinary_path (P := P) ready.checked allocated.entry) allocated.tables allocated.targets allocated.links invoked

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs.Core
