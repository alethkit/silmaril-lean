module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms

import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Proofs.Lime1

open Execution
open Wasm.Lime1.Execution
open Execution.Runtime (Value)
open Execution.Runtime (Frame)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Frame} {index : FuncIdx} {args : List Value} {value : BitVec 32}

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

private theorem invoke_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.site.limeInvoke s outer args) dst ↔ dst = entry.limeRead s outer args := by
  have count : args.length = entry.site.cont.owner.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length ready.typed)
  exact CallFrame.lime_invoke_wasm_exact (caller := outer) (dst := dst) allocated count

private theorem read_iff (read : entry.Condition args value) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeRead s outer args) dst ↔ dst = entry.limeTest s outer args value := by
  let tail := .source entry.limeIf :: entry.tail.map Graph.limeEmit
  let code := values entry.site.cont.owner.initial ++ .source (.localGet entry.condition) :: tail
  have rendered : expression entry.limeFunc.body = code := by
    rw [Entry.limeFunc]
    rw [expression_prefix]
    change _ ++ .source (.localGet entry.condition) :: .source entry.limeIf ::
      expression (Graph.Op.emitList Graph.limeCodeSyntax entry.tail) = code
    rw [expression_tail entry.site.cont.owner]
  have stays (out : List Admin) : ¬ PureStep (entry.site.frame args).module.types [.label entry.site.cont.owner.declaration.results.length [] code] out :=
    Computed.lime_label_stays (head := .source (.localGet entry.condition))
      rfl (by simp) (by simp) (by simp)
  simp only [Entry.limeRead, rendered]
  rw [Context.Resume.lime_wrap_step_iff stays]
  have reduction : Prefix.Reduce (entry.site.frame args).locals entry.site.cont.owner.initial
      (.get entry.condition) (.values (entry.site.cont.owner.initial ++ [.int .i32 value])) := .get read
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, step, rfl⟩ := (Prefix.lime_step_iff (s := s) (f := entry.site.frame args)
      (stack := entry.site.cont.owner.initial) (op := .get entry.condition) (tail := tail)).mp move
    rw [Prefix.reduce_unique step reduction]
    rfl
  · rintro rfl
    exact ⟨_, Prefix.lime_step_iff.mpr ⟨_, reduction, rfl⟩, rfl⟩

private theorem selected_code (s : Store H) (outer : Frame) (args : List Value) (value : BitVec 32) :
    let arms := entry.arms entry.inside.body.lime (Graph.Op.emitList Graph.limeCodeSyntax entry.alternate)
    entry.limeSelected s outer args value =
      entry.site.cont.limeWrap outer ⟨s, entry.site.frame args,
        values entry.site.cont.owner.initial ++ .source (.block (Blocks.limeType entry.result)
          (if value = 0 then arms.2 else arms.1)) :: entry.tail.map Graph.limeEmit⟩ := by
  have site :
      entry.site.limeBody s outer args = entry.site.cont.limeWrap outer ⟨s, entry.site.frame args,
        values entry.site.cont.owner.initial ++
          .source (.block (Blocks.limeType entry.result) entry.inside.body.lime) :: entry.tail.map Graph.limeEmit⟩ := by
    unfold GraphEntry.Entry.limeBody
    have rendered : expression entry.site.limeFunc.body = values entry.site.cont.owner.initial ++
        .source (.block (Blocks.limeType entry.result) entry.inside.body.lime) :: entry.tail.map Graph.limeEmit := by
      change expression (_ ++ _) = _
      rw [expression_prefix]
      rw [site_body]
      change _ ++ .source (.block (Blocks.limeType entry.result) entry.inside.body.lime) ::
        expression (Graph.Op.emitList Graph.limeCodeSyntax entry.tail) = _
      rw [expression_tail entry.site.cont.owner]
    rw [rendered]
  have alternate :
      Graph.limeConfig s outer entry.site.cont.target (entry.alternatePhase args) =
        entry.site.cont.limeWrap outer ⟨s, entry.site.frame args,
          values entry.site.cont.owner.initial ++
            .source (.block (Blocks.limeType entry.result) (Graph.Op.emitList Graph.limeCodeSyntax entry.alternate)) ::
              entry.tail.map Graph.limeEmit⟩ := by
    rfl
  cases arm : entry.siteOnTrue <;> by_cases zero : value = (0#32) <;>
    simp [Entry.limeSelected, Entry.choosesSite, Entry.arms, arm, zero, site, alternate]

private theorem test_iff (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeTest s outer args value) dst ↔ dst = entry.limeSelected s outer args value := by
  let arms := entry.arms entry.inside.body.lime (Graph.Op.emitList Graph.limeCodeSyntax entry.alternate)
  let code := values (entry.site.cont.owner.initial ++ [.int .i32 value]) ++ .source entry.limeIf :: entry.tail.map Graph.limeEmit
  have stays (out : List Admin) : ¬ PureStep (entry.site.frame args).module.types [.label entry.site.cont.owner.declaration.results.length [] code] out := by
    unfold code
    exact Computed.lime_label_stays (head := .source entry.limeIf)
      rfl (by simp [Entry.limeIf]) (by simp [Entry.limeIf])
      (by simp [Entry.limeIf])
  change Step CallFrame.limeNoHost (entry.site.cont.limeWrap outer ⟨s, entry.site.frame args, code⟩) dst ↔ _
  rw [Context.Resume.lime_wrap_step_iff stays, selected_code]
  have raw (mid : Config H) := Computed.lime_if_iff (s := s) (f := entry.site.frame args)
    (saved := entry.site.cont.owner.initial) (condition := value) (bt := Blocks.limeType entry.result) (thenBody := arms.1) (elseBody := arms.2)
    (rest := entry.tail.map Graph.limeEmit) (dst := mid)

  have exactStep (mid : Config H) :
      Step CallFrame.limeNoHost ⟨s, entry.site.frame args, code⟩ mid ↔
        mid = ⟨s, entry.site.frame args, values entry.site.cont.owner.initial ++ .source (.block (Blocks.limeType entry.result)
          (if value = 0 then arms.2 else arms.1)) :: entry.tail.map Graph.limeEmit⟩ := by
    exact raw mid
  simp only [exactStep, exists_eq_left, arms]

theorem front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance) (read : entry.Condition args value) :
    (limeSource s outer index args :: entry.limeFront s outer args value ++
      [entry.limeSelected s outer args value]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨invoke_iff ready allocated,
    List.isChain_cons_cons.mpr ⟨read_iff read, List.isChain_pair.mpr test_iff⟩⟩⟩
  intro dst
  exact Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) ready.resolves

theorem alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value) (select : entry.choosesSite value = false)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ limeSource s outer index args :: entry.limeFront s outer args value ∨
      ∃ phase, program.FrameRuns entry.site.cont.address (entry.alternatePhase args) phase ∧
        Graph.Admitted program entry.site.cont.owner phase ∧
        dst = Graph.limeConfig s outer entry.site.cont.target phase := by
  have path := front_exact ready allocated read
  simp only [Entry.limeSelected, select, Bool.false_eq_true, ite_false] at path
  have checked := (Bool.and_eq_true_iff.mp (site_checked ready).source).1
  exact (Context.Resume.prefix_run_iff _ _ path).trans (or_congr Iff.rfl
    (Context.linked_runs checked ready.found (Graph.limeConfig s outer entry.site.cont.target) (Step CallFrame.limeNoHost)
      (fun h entered => Graph.lime_entered_frame_step_iff checked links ready.found rfl h entered)
      (alternate_admitted ready) trivial))

private theorem enters_site (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true) :
    (limeSource s outer index args :: entry.limeFront s outer args value ++
      [entry.site.limeBody s outer args]).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  simpa only [Entry.limeSelected, select, ite_true] using front_exact ready allocated read

theorem site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args value) ++ entry.site.limeSitePath s outer args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.limeConfig call s outer phase :=
  GraphEntry.lime_run_via atSite .body (limeSource s outer index args) (entry.limeFront s outer args value)
    (enters_site ready allocated read select) tableAllocated targets links invoked

theorem lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.LimeAllocated tables s)
    (targets : active.binding.site.LimeAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ ((limeSource s outer index args :: entry.limeFront s outer args value) ++ entry.site.limeSitePath s outer args active out states).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.limeTrapStart active) phase ∧
        dst = entry.site.limeCleanup s outer active.caller phase :=
  GraphEntry.lime_trap_run_via atSite .body (limeSource s outer index args) (entry.limeFront s outer args value)
    (enters_site ready allocated read select) tableAllocated targets resolved trap

theorem operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.limeInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeSource s outer index args) dst ↔
      dst ∈ (limeSource s outer index args :: entry.limeFront s outer args value) ++ entry.site.limeInside s outer args states ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.limeEmit saved (entry.site.limeSiteCode rest)) phase ∧
        dst = entry.site.limeCleanup s outer (entry.site.frame args) phase :=
  GraphEntry.lime_operand_trap_run_via .body (limeSource s outer index args) (entry.limeFront s outer args value)
    (enters_site ready allocated read select) trace

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Proofs.Lime1
