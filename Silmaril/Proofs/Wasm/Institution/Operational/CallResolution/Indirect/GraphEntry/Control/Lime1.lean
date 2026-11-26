module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Proofs.Lime1

open Execution
open Wasm.Lime1.Execution
open Execution.Runtime (Value)
open Execution.Runtime (Frame)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Context.Resume (Block)
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Frame} {index : FuncIdx} {args : List Value}

private theorem expression_prefix (fn : Graph.Function) (code : Wasm.Lime1.Expr) :
    expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++ code) =
      values fn.initial ++ expression code := by
  have literals := Graph.lime_body_expression { fn with code := [] }
  change expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++ []) = values fn.initial ++ [] at literals
  simp only [List.append_nil, expression, List.map_append] at literals ⊢
  rw [literals]

private theorem expression_tail (fn : Graph.Function) (code : List Graph.Op) :
    expression (Graph.Op.emitList Graph.limeCodeSyntax code) = code.map Graph.limeEmit :=
  Graph.lime_body_expression { fn with initial := [], code := code }

private theorem block_code (block : Block) (rest : List Node) :
    expression (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr (⟨block, none⟩ :: rest)) =
      .source (.block (Blocks.limeType block.result) (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest)) ::
        block.tail.map Graph.limeEmit := by
  change .source (.block (Blocks.limeType block.result) _) :: expression (Graph.Op.emitList Graph.limeCodeSyntax block.tail) = _
  rw [expression_tail entry.cont.owner]
  rfl

private theorem read_code (block : Block) (choice : Choice) (rest : List Node) :
    expression (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr (⟨block, some choice⟩ :: rest)) =
      .source (.localGet choice.condition) ::
      .source (Node.switch Graph.limeCodeSyntax block choice (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest)) ::
        block.tail.map Graph.limeEmit := by
  change .source (.localGet choice.condition) :: .source _ ::
    expression (Graph.Op.emitList Graph.limeCodeSyntax block.tail) = _
  rw [expression_tail entry.cont.owner]
  rfl

private theorem step_under (entered : List Block) {before after dst : Config H}
    (stays : ∀ n out, ¬ PureStep before.frame.module.types [.label n [] before.code] out)
    (edge : ∀ target, Step CallFrame.limeNoHost before target ↔ target = after) :
    Step CallFrame.limeNoHost ((entry.withBlocks entered).limeSiteWrap outer before) dst ↔
      dst = (entry.withBlocks entered).limeSiteWrap outer after := by
  rw [Context.Resume.lime_site_step_iff stays]
  simp only [edge, exists_eq_left]

private theorem block_iff (entered : List Block) (block : Block) (rest : List Node) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limePosition s outer args (.pending entered (⟨block, none⟩ :: rest))) dst ↔
      dst = entry.limePosition s outer args (.pending (entered ++ [block]) rest) := by
  let body := entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest
  let saved := entry.saved entered
  let tail := block.tail.map Graph.limeEmit
  let before : Config H := ⟨s, entry.site.frame args, values saved ++ .source (.block (Blocks.limeType block.result) body) :: tail⟩
  let after : Config H := ⟨s, entry.site.frame args, values saved ++ .label block.result.toList.length [] (expression body) :: tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ PureStep before.frame.module.types [.label n [] before.code] out :=
    Computed.lime_label_stays (head := .source (.block (Blocks.limeType block.result) body)) rfl (by simp) (by simp) (by simp)
  have edge (mid : Config H) : Step CallFrame.limeNoHost before mid ↔ mid = after :=
    Computed.lime_block_iff (s := s) (f := entry.site.frame args) (dst := mid)
      (result := block.result) (body := body) (rest := tail) (stack := saved)
  simp only [Entry.limePosition, block_code]
  refine (step_under entered stays edge).trans ?_
  have scopes := scopes_append_one entered block entry.cont.owner.initial
  simp [Context.Resume.Continuation.limeSiteWrap, Context.Resume.Continuation.limeWrap, Entry.withBlocks,
    Context.Resume.Continuation.scopes, scopes, Context.limeNestWith, Context.Resume.Block.scope,
    saved, Entry.saved, after, body, tail, values]

private theorem read_iff (entered : List Block) (block : Block) (choice : Choice) (rest : List Node)
    (value : BitVec 32) (read : (entry.site.frame args).locals[choice.condition.toNat]? = some (.int .i32 value))
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limePosition s outer args (.pending entered (⟨block, some choice⟩ :: rest))) dst ↔
      dst = entry.limePosition s outer args (.test entered block choice rest value) := by
  let body := entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest
  let tail := .source (Node.switch Graph.limeCodeSyntax block choice body) :: block.tail.map Graph.limeEmit
  let before : Config H := ⟨s, entry.site.frame args, values (entry.saved entered) ++ .source (.localGet choice.condition) :: tail⟩
  let after : Config H := ⟨s, entry.site.frame args, values (entry.saved entered ++ [.int .i32 value]) ++ tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ PureStep before.frame.module.types [.label n [] before.code] out :=
    Computed.lime_label_stays (head := .source (.localGet choice.condition)) rfl (by simp) (by simp) (by simp)
  have reduction : Prefix.Reduce (entry.site.frame args).locals (entry.saved entered)
      (.get choice.condition) (.values (entry.saved entered ++ [.int .i32 value])) := .get read
  have edge (mid : Config H) : Step CallFrame.limeNoHost before mid ↔ mid = after := by
    refine (Prefix.lime_step_iff (s := s) (f := entry.site.frame args) (stack := entry.saved entered)
      (op := .get choice.condition) (tail := tail)).trans ⟨?_, ?_⟩
    · rintro ⟨out, step, rfl⟩
      rw [Prefix.reduce_unique step reduction]
      rfl
    · rintro rfl
      exact ⟨_, reduction, rfl⟩
  simp only [Entry.limePosition, read_code]
  exact step_under entered stays edge

private theorem test_iff (entered : List Block) (block : Block) (choice : Choice) (rest : List Node)
    (value : BitVec 32) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limePosition s outer args (.test entered block choice rest value)) dst ↔
      dst = (entry.withBlocks entered).limeSiteWrap outer ⟨s, entry.site.frame args,
        values (entry.saved entered) ++ .source (.block (Blocks.limeType block.result)
          (if choice.takesSite value then entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest
           else Graph.Op.emitList Graph.limeCodeSyntax choice.alternate)) :: block.tail.map Graph.limeEmit⟩ := by
  let body := entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest
  let saved := entry.saved entered
  let arms := choice.arms body (Graph.Op.emitList Graph.limeCodeSyntax choice.alternate)
  let instr : Admin := .source (Node.switch Graph.limeCodeSyntax block choice body)
  let tail := block.tail.map Graph.limeEmit
  let before : Config H := ⟨s, entry.site.frame args, values (saved ++ [.int .i32 value]) ++ instr :: tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ PureStep before.frame.module.types [.label n [] before.code] out :=
    Computed.lime_label_stays (head := .source (.if_ (Blocks.limeType block.result) arms.1 arms.2))
      rfl (by simp) (by simp) (by simp)
  have edge (mid : Config H) := Computed.lime_if_iff (s := s) (f := entry.site.frame args)
    (saved := saved) (condition := value) (bt := Blocks.limeType block.result) (thenBody := arms.1) (elseBody := arms.2) (rest := tail) (dst := mid)
  change Step CallFrame.limeNoHost ((entry.withBlocks entered).limeSiteWrap outer before) dst ↔ _
  refine (step_under entered stays edge).trans ?_
  rw [show (if value = 0 then arms.2 else arms.1) = _ from selected_arm choice value _ _]

private theorem alternate_render (entered : List Block) (block : Block) (choice : Choice) :
    entry.limeEnd s outer args (.alternate entered (Node.alternateCode block choice)) =
      (entry.withBlocks entered).limeSiteWrap outer ⟨s, entry.site.frame args,
        values (entry.saved entered) ++
          .source (.block (Blocks.limeType block.result) (Graph.Op.emitList Graph.limeCodeSyntax choice.alternate)) ::
            block.tail.map Graph.limeEmit⟩ := by
  let body := Graph.Body.running (entry.saved entered) (Node.alternateCode block choice)
  let cfg : Config H := ⟨s, entry.site.frame args, body.render Graph.limeAdmin⟩
  let scopes := Block.scopes entered entry.cont.owner.initial
  have code := Context.Resume.lime_plug_code entered entry.cont.owner.initial body cfg rfl
  have same (xs : List (Blocks.Context.Scope Graph.Op)) :
      (Context.limeNest xs cfg).store = s ∧ (Context.limeNest xs cfg).frame = entry.site.frame args := by
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ ih => exact ih
  obtain ⟨store, frame⟩ := same scopes
  change _ = entry.cont.limeWrap outer (Context.limeNest scopes cfg)
  unfold Context.Resume.Continuation.limeWrap
  change (Context.limeNest scopes cfg).code = _ at code
  rw [store, frame, code]
  rfl

private theorem control_chain {entered nodes states endpoint}
    (trace : Trace (entry.site.frame args).locals entered nodes states endpoint) :
    (states.map (entry.limePosition s outer args) ++ [entry.limeEnd s outer args endpoint]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  let render := entry.limePosition s outer args
  let finish := entry.limeEnd s outer args
  induction trace with
  | done => exact .singleton _
  | block next ih =>
    apply ih.cons
    have first := trace_head render finish (fun _ => rfl) next
    intro b found dst
    rw [first] at found
    obtain rfl := Option.mem_some.mp found
    exact block_iff _ _ _ dst
  | @taken entered block choice rest value states endpoint read select next ih =>
    refine List.isChain_cons_cons.mpr ⟨read_iff _ _ _ _ _ read, ih.cons ?_⟩
    have first := trace_head render finish (fun _ => rfl) next
    intro b found dst
    rw [first] at found
    obtain rfl := Option.mem_some.mp found
    simpa only [select, ite_true, render, Entry.limePosition, block_code] using (test_iff (entry := entry) (s := s) (outer := outer) (args := args) entered block choice rest value dst)
  | @alternate entered block choice rest value read select =>
    refine List.isChain_cons_cons.mpr ⟨read_iff _ _ _ _ _ read, List.isChain_pair.mpr ?_⟩
    intro dst
    rw [alternate_render]
    simpa only [select, Bool.false_eq_true, ite_false, render, Entry.limePosition] using (test_iff (entry := entry) (s := s) (outer := outer) (args := args) entered block choice rest value dst)

private theorem invoke_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.site.limeInvoke s outer args) dst ↔
      dst = entry.limePosition s outer args (.pending [] entry.nodes) := by
  have count : args.length = entry.cont.owner.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length ready.typed)
  have enter := CallFrame.lime_invoke_wasm_exact (caller := outer) (dst := dst) allocated count
  have body := expression_prefix entry.cont.owner
    (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr entry.nodes)
  change _ ↔ dst = entry.cont.limeWrap outer ⟨s, entry.site.frame args, expression entry.limeFunc.body⟩ at enter
  rw [Entry.limeFunc, body] at enter
  exact enter

theorem front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states endpoint} (trace : entry.Trace args states endpoint) :
    (limeSource s outer index args :: entry.limeFront s outer args states ++
      [entry.limeEnd s outer args endpoint]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have chain := control_chain (s := s) (outer := outer) trace
  refine List.isChain_cons_cons.mpr ⟨?_, chain.cons ?_⟩
  · intro dst
    exact Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) ready.resolves
  · have head := trace_head (entry.limePosition s outer args) (entry.limeEnd s outer args) (fun _ => rfl) trace
    intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact invoke_iff ready allocated dst

private theorem site_front (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states entered} (trace : entry.Trace args states (.site entered)) :
    (limeSource s outer index args :: entry.limeFront s outer args states ++
      [entry.site.limeEntrance s outer args .operands]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have eq : entered = entry.site.cont.blocks := site_spine trace
  have endpoint : entry.limeEnd s outer args (.site entered) = entry.site.limeEntrance s outer args .operands := by
    rw [eq]
    change (entry.withBlocks entry.site.cont.blocks).limeSiteWrap outer ⟨s, entry.site.frame args,
      values (entry.saved entry.site.cont.blocks) ++ expression entry.site.siteBody.lime⟩ = _
    rw [GraphEntry.lime_site_code]
    rfl
  rw [← endpoint]
  exact front_exact ready allocated trace

theorem alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {states entered code} (trace : entry.Trace args states (.alternate entered code))
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ limeSource s outer index args :: entry.limeFront s outer args states ∨
      ∃ phase, program.FrameRuns entry.cont.address (entry.alternatePhase args entered code) phase ∧
        Graph.Admitted program entry.cont.owner phase ∧ dst = Graph.limeConfig s outer entry.cont.target phase := by
  have path := front_exact ready allocated trace
  have checked := (Bool.and_eq_true_iff.mp (site_checked ready).source).1
  exact (Context.Resume.prefix_run_iff _ _ path).trans (or_congr Iff.rfl
    (Context.linked_runs checked ready.found (Graph.limeConfig s outer entry.cont.target) (Step CallFrame.limeNoHost)
      (fun h entered => Graph.lime_entered_frame_step_iff checked links ready.found rfl h entered)
      (alternate_admitted ready trace) trivial))

theorem site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args path) ++ entry.site.limeSitePath s outer args active (.resolved call.address) states .operands ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.limeConfig call s outer phase :=
  GraphEntry.lime_run_via atSite .operands (limeSource s outer index args) (entry.limeFront s outer args path)
    (site_front ready allocated control) tableAllocated targets links invoked

theorem lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ ((limeSource s outer index args :: entry.limeFront s outer args path) ++ entry.site.limeSitePath s outer args active out states .operands).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.limeTrapStart active) phase ∧
        dst = entry.site.limeCleanup s outer active.caller phase :=
  GraphEntry.lime_trap_run_via atSite .operands (limeSource s outer index args) (entry.limeFront s outer args path)
    (site_front ready allocated control) tableAllocated targets resolved trap

theorem operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args path) ++ entry.site.limeInside s outer args states .operands ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.limeEmit saved (entry.site.limeSiteCode rest)) phase ∧
        dst = entry.site.limeCleanup s outer (entry.site.frame args) phase :=
  GraphEntry.lime_operand_trap_run_via .operands (limeSource s outer index args) (entry.limeFront s outer args path)
    (site_front ready allocated control) trace

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Proofs.Lime1
