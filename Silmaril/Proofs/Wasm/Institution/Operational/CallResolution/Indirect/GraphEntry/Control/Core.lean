module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)

open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Context.Resume (Block)
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Runtime.Frame} {index : FuncIdx} {args : List Value}

private theorem expression_prefix (fn : Graph.Function) (code : List Instr) :
    expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++ code) =
      coreValues fn.initial ++ expression code := by
  have literals := Graph.core_body_expression { fn with code := [] }
  change expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++ []) = coreValues fn.initial ++ [] at literals
  simp only [List.append_nil, expression, List.map_append] at literals ⊢
  rw [literals]

private theorem expression_tail (fn : Graph.Function) (code : List Graph.Op) :
    expression (Graph.Op.emitList Graph.coreCodeSyntax code) = code.map Graph.coreEmit :=
  Graph.core_body_expression { fn with initial := [], code := code }

private theorem block_code (block : Block) (rest : List Node) :
    expression (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr (⟨block, none⟩ :: rest)) =
      .plain (.block (Blocks.coreType block.result) (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest)) ::
        block.tail.map Graph.coreEmit := by
  change .plain (.block (Blocks.coreType block.result) _) :: expression (Graph.Op.emitList Graph.coreCodeSyntax block.tail) = _
  rw [expression_tail entry.cont.owner]
  rfl

private theorem read_code (block : Block) (choice : Choice) (rest : List Node) :
    expression (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr (⟨block, some choice⟩ :: rest)) =
      .plain (.localGet choice.condition) ::
      .plain (Node.switch Graph.coreCodeSyntax block choice (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest)) ::
        block.tail.map Graph.coreEmit := by
  change .plain (.localGet choice.condition) :: .plain _ ::
    expression (Graph.Op.emitList Graph.coreCodeSyntax block.tail) = _
  rw [expression_tail entry.cont.owner]
  rfl

private theorem step_under (entered : List Block) {before after dst : Config H}
    (stays : ∀ n out, ¬ LabelExit n [] before.code out)
    (edge : ∀ target, Step P noHost before target ↔ target = after) :
    Step P noHost ((entry.withBlocks entered).coreSiteWrap outer before) dst ↔
      dst = (entry.withBlocks entered).coreSiteWrap outer after := by
  rw [Context.Resume.core_site_step_iff stays]
  simp only [edge, exists_eq_left]

private theorem block_iff (entered : List Block) (block : Block) (rest : List Node) (dst : Config H) :
    Step P noHost (entry.corePosition s outer args (.pending entered (⟨block, none⟩ :: rest))) dst ↔
      dst = entry.corePosition s outer args (.pending (entered ++ [block]) rest) := by
  let body := entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest
  let saved := entry.saved entered
  let tail := block.tail.map Graph.coreEmit
  let before : Config H := ⟨s, (entry.site.frame args).toCore, coreValues saved ++ .plain (.block (Blocks.coreType block.result) body) :: tail⟩
  let after : Config H := ⟨s, (entry.site.frame args).toCore, coreValues saved ++ .label block.result.toList.length [] (expression body) :: tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ LabelExit n [] before.code out :=
    Computed.core_label_stays (head := .plain (.block (Blocks.coreType block.result) body)) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  have edge (mid : Config H) : Step P noHost before mid ↔ mid = after :=
    Blocks.core_context_entry_iff (P := P) (s := s) (f := (entry.site.frame args).toCore) (dst := mid)
      (result := block.result) (body := body) (rest := tail) (saved := saved.map Value.toCore)
  simp only [Entry.corePosition, block_code]
  refine (step_under entered stays edge).trans ?_
  have scopes := scopes_append_one entered block entry.cont.owner.initial
  simp [Context.Resume.Continuation.coreSiteWrap, Context.Resume.Continuation.coreWrap, Entry.withBlocks,
    Context.Resume.Continuation.scopes, scopes, Context.coreNestWith, Context.Resume.Block.scope,
    saved, Entry.saved, after, body, tail, coreValues]

private theorem read_iff (entered : List Block) (block : Block) (choice : Choice) (rest : List Node)
    (value : BitVec 32) (read : (entry.site.frame args).locals[choice.condition.toNat]? = some (.int .i32 value))
    (dst : Config H) :
    Step P noHost (entry.corePosition s outer args (.pending entered (⟨block, some choice⟩ :: rest))) dst ↔
      dst = entry.corePosition s outer args (.test entered block choice rest value) := by
  let body := entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest
  let tail := .plain (Node.switch Graph.coreCodeSyntax block choice body) :: block.tail.map Graph.coreEmit
  let before : Config H := ⟨s, (entry.site.frame args).toCore, coreValues (entry.saved entered) ++ .plain (.localGet choice.condition) :: tail⟩
  let after : Config H := ⟨s, (entry.site.frame args).toCore, coreValues (entry.saved entered ++ [.int .i32 value]) ++ tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ LabelExit n [] before.code out :=
    Computed.core_label_stays (head := .plain (.localGet choice.condition)) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  have reduction : Prefix.Reduce (entry.site.frame args).locals (entry.saved entered)
      (.get choice.condition) (.values (entry.saved entered ++ [.int .i32 value])) := .get read
  have edge (mid : Config H) : Step P noHost before mid ↔ mid = after := by
    refine (Prefix.core_step_iff (P := P) (s := s) (f := entry.site.frame args) (stack := entry.saved entered)
      (op := .get choice.condition) (tail := tail)).trans ⟨?_, ?_⟩
    · rintro ⟨out, step, rfl⟩
      rw [Prefix.reduce_unique step reduction]
      rfl
    · rintro rfl
      exact ⟨_, reduction, rfl⟩
  simp only [Entry.corePosition, read_code]
  exact step_under entered stays edge

private theorem test_iff (entered : List Block) (block : Block) (choice : Choice) (rest : List Node)
    (value : BitVec 32) (dst : Config H) :
    Step P noHost (entry.corePosition s outer args (.test entered block choice rest value)) dst ↔
      dst = (entry.withBlocks entered).coreSiteWrap outer ⟨s, (entry.site.frame args).toCore,
        coreValues (entry.saved entered) ++ .plain (.block (Blocks.coreType block.result)
          (if choice.takesSite value then entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest
           else Graph.Op.emitList Graph.coreCodeSyntax choice.alternate)) :: block.tail.map Graph.coreEmit⟩ := by
  let body := entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest
  let saved := entry.saved entered
  let arms := choice.arms body (Graph.Op.emitList Graph.coreCodeSyntax choice.alternate)
  let instr : Admin := .plain (Node.switch Graph.coreCodeSyntax block choice body)
  let tail := block.tail.map Graph.coreEmit
  let before : Config H := ⟨s, (entry.site.frame args).toCore, coreValues (saved ++ [.int .i32 value]) ++ instr :: tail⟩
  have stays (n : Nat) (out : List Admin) : ¬ LabelExit n [] before.code out :=
    Computed.core_label_stays (head := .plain (.if_ (Blocks.coreType block.result) arms.1 arms.2))
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  have edge (mid : Config H) := Computed.core_if_iff (P := P) (s := s) (f := (entry.site.frame args).toCore)
    (saved := saved.map Value.toCore) (condition := value) (bt := Blocks.coreType block.result) (thenBody := arms.1) (elseBody := arms.2) (rest := tail) (dst := mid)
  have repr : (Value.int .i32 value).toCore = .num ⟨.int .i32, value⟩ := rfl
  have lift (mid : Config H) : Step P noHost before mid ↔ mid =
      ⟨s, (entry.site.frame args).toCore, coreValues saved ++
        .plain (.block (Blocks.coreType block.result) (if value = 0 then arms.2 else arms.1)) :: tail⟩ := by
    simpa only [before, coreValues, List.map_append, List.map_singleton, repr, instr, Node.switch,
      Graph.coreCodeSyntax, Function.comp_def, arms] using edge mid
  change Step P noHost ((entry.withBlocks entered).coreSiteWrap outer before) dst ↔ _
  refine (step_under entered stays lift).trans ?_
  rw [show (if value = 0 then arms.2 else arms.1) = _ from selected_arm choice value _ _]

private theorem alternate_render (entered : List Block) (block : Block) (choice : Choice) :
    entry.coreEnd s outer args (.alternate entered (Node.alternateCode block choice)) =
      (entry.withBlocks entered).coreSiteWrap outer ⟨s, (entry.site.frame args).toCore,
        coreValues (entry.saved entered) ++
          .plain (.block (Blocks.coreType block.result) (Graph.Op.emitList Graph.coreCodeSyntax choice.alternate)) ::
            block.tail.map Graph.coreEmit⟩ := by
  let body := Graph.Body.running (entry.saved entered) (Node.alternateCode block choice)
  let cfg : Config H := ⟨s, (entry.site.frame args).toCore, body.render Graph.coreAdmin⟩
  let scopes := Block.scopes entered entry.cont.owner.initial
  have code := Context.Resume.core_plug_code entered entry.cont.owner.initial body cfg rfl
  have same (xs : List (Blocks.Context.Scope Graph.Op)) :
      (Context.coreNest xs cfg).store = s ∧ (Context.coreNest xs cfg).frame = (entry.site.frame args).toCore := by
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ ih => exact ih
  obtain ⟨store, frame⟩ := same scopes
  change _ = entry.cont.coreWrap outer (Context.coreNest scopes cfg)
  unfold Context.Resume.Continuation.coreWrap
  change (Context.coreNest scopes cfg).code = _ at code
  rw [store, frame, code]
  rfl

private theorem control_chain {entered nodes states endpoint}
    (trace : Trace (entry.site.frame args).locals entered nodes states endpoint) :
    (states.map (entry.corePosition s outer args) ++ [entry.coreEnd s outer args endpoint]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  let render := entry.corePosition s outer args
  let finish := entry.coreEnd s outer args
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
    simpa only [select, ite_true, render, Entry.corePosition, block_code] using (test_iff (entry := entry) (s := s) (outer := outer) (args := args) (P := P) entered block choice rest value dst)
  | @alternate entered block choice rest value read select =>
    refine List.isChain_cons_cons.mpr ⟨read_iff _ _ _ _ _ read, List.isChain_pair.mpr ?_⟩
    intro dst
    rw [alternate_render]
    simpa only [select, Bool.false_eq_true, ite_false, render, Entry.corePosition] using (test_iff (entry := entry) (s := s) (outer := outer) (args := args) (P := P) entered block choice rest value dst)

private theorem invoke_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance) (dst : Config H) :
    Step P noHost (entry.site.coreInvoke s outer args) dst ↔
      dst = entry.corePosition s outer args (.pending [] entry.nodes) := by
  have enter := Sequence.wasm_entry_iff (P := P) (caller := outer) (dst := dst) allocated ready.typed
  have frame := Sequence.core_frame_forCall entry.cont.owner.declaration.module args entry.cont.owner.declaration.locals
  change Core.Frame.forCall entry.cont.owner.declaration.module.toCore (args.map Value.toCore) entry.coreFunc.locals =
    (entry.site.frame args).toCore at frame
  rw [frame] at enter
  have body := expression_prefix entry.cont.owner
    (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr entry.nodes)
  change _ ↔ dst = entry.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore, expression entry.coreFunc.body⟩ at enter
  rw [Entry.coreFunc, body] at enter
  exact enter

theorem front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states endpoint} (trace : entry.Trace args states endpoint) :
    (coreSource s outer index args :: entry.coreFront s outer args states ++
      [entry.coreEnd s outer args endpoint]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have chain := control_chain (s := s) (outer := outer) (P := P) trace
  refine List.isChain_cons_cons.mpr ⟨?_, chain.cons ?_⟩
  · intro dst
    exact Computed.core_direct_call_iff (s := s) (P := P) (stack := args) (tail := []) ready.resolves allocated
  · have head := trace_head (entry.corePosition s outer args) (entry.coreEnd s outer args) (fun _ => rfl) trace
    intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact invoke_iff ready allocated dst

private theorem site_front (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states entered} (trace : entry.Trace args states (.site entered)) :
    (coreSource s outer index args :: entry.coreFront s outer args states ++
      [entry.site.coreEntrance s outer args .operands]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have eq : entered = entry.site.cont.blocks := site_spine trace
  have endpoint : entry.coreEnd s outer args (.site entered) = entry.site.coreEntrance s outer args .operands := by
    rw [eq]
    change (entry.withBlocks entry.site.cont.blocks).coreSiteWrap outer ⟨s, (entry.site.frame args).toCore,
      coreValues (entry.saved entry.site.cont.blocks) ++ expression entry.site.siteBody.core⟩ = _
    rw [GraphEntry.core_site_code]
    rfl
  rw [← endpoint]
  exact front_exact ready allocated trace

theorem alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {states entered code} (trace : entry.Trace args states (.alternate entered code))
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ coreSource s outer index args :: entry.coreFront s outer args states ∨
      ∃ phase, program.FrameRuns entry.cont.address (entry.alternatePhase args entered code) phase ∧
        Graph.Admitted program entry.cont.owner phase ∧ dst = Graph.coreConfig s outer entry.cont.target phase := by
  have path := front_exact (P := P) ready allocated trace
  have checked := (Bool.and_eq_true_iff.mp (site_checked ready).source).1
  exact (Context.Resume.prefix_run_iff _ _ path).trans (or_congr Iff.rfl
    (Context.linked_runs checked ready.found (Graph.coreConfig s outer entry.cont.target) (Step P noHost)
      (fun h entered => Graph.core_entered_frame_step_iff checked links ready.found rfl h entered)
      (alternate_admitted ready trace) trivial))

theorem site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args path) ++ entry.site.coreSitePath s outer args active (.resolved call.address) states .operands ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.coreConfig call s outer phase :=
  GraphEntry.core_run_via atSite .operands (coreSource s outer index args) (entry.coreFront s outer args path)
    (site_front ready allocated control) tableAllocated targets links invoked

theorem lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ ((coreSource s outer index args :: entry.coreFront s outer args path) ++ entry.site.coreSitePath s outer args active out states .operands).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.coreTrapStart active out) phase ∧
        dst = entry.site.coreCleanup s outer active.caller phase :=
  GraphEntry.core_trap_run_via atSite .operands (coreSource s outer index args) (entry.coreFront s outer args path)
    (site_front ready allocated control) tableAllocated targets resolved trap

theorem operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance)
    {path entered} (control : entry.Trace args path (.site entered))
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args path) ++ entry.site.coreInside s outer args states .operands ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.coreEmit saved (entry.site.coreSiteCode rest)) phase ∧
        dst = entry.site.coreCleanup s outer (entry.site.frame args) phase :=
  GraphEntry.core_operand_trap_run_via .operands (coreSource s outer index args) (entry.coreFront s outer args path)
    (site_front ready allocated control) trace

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Proofs.Core
