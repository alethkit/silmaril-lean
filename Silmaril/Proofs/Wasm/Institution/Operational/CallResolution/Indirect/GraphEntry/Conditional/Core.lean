module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms

import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)

open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Execution.Runtime.Frame} {index : FuncIdx} {args : List Value} {value : BitVec 32}

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

private theorem invoke_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance) (dst : Config H) :
    Step P noHost (entry.site.coreInvoke s outer args) dst ↔ dst = entry.coreRead s outer args := by
  have enter := Sequence.wasm_entry_iff (P := P) (caller := outer) (dst := dst) allocated ready.typed
  have frame := Sequence.core_frame_forCall entry.site.cont.owner.declaration.module args entry.site.cont.owner.declaration.locals
  change Core.Frame.forCall entry.site.cont.owner.declaration.module.toCore (args.map Value.toCore) entry.coreFunc.locals =
    (entry.site.frame args).toCore at frame
  rw [frame] at enter
  exact enter

private theorem read_iff (read : entry.Condition args value) (dst : Config H) :
    Step P noHost (entry.coreRead s outer args) dst ↔ dst = entry.coreTest s outer args value := by
  let tail := .plain entry.coreIf :: entry.tail.map Graph.coreEmit
  let code := coreValues entry.site.cont.owner.initial ++ .plain (.localGet entry.condition) :: tail
  have rendered : expression entry.coreFunc.body = code := by
    rw [Entry.coreFunc]
    rw [expression_prefix]
    change _ ++ .plain (.localGet entry.condition) :: .plain entry.coreIf ::
      expression (Graph.Op.emitList Graph.coreCodeSyntax entry.tail) = code
    rw [expression_tail entry.site.cont.owner]
  have stays (out : List Admin) : ¬ LabelExit entry.site.cont.owner.declaration.results.length [] code out :=
    Computed.core_label_stays (head := .plain (.localGet entry.condition))
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  simp only [Entry.coreRead, rendered]
  rw [Context.Resume.core_wrap_step_iff stays]
  have reduction : Prefix.Reduce (entry.site.frame args).locals entry.site.cont.owner.initial
      (.get entry.condition) (.values (entry.site.cont.owner.initial ++ [.int .i32 value])) := .get read
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, step, rfl⟩ := (Prefix.core_step_iff (P := P) (s := s) (f := entry.site.frame args)
      (stack := entry.site.cont.owner.initial) (op := .get entry.condition) (tail := tail)).mp move
    rw [Prefix.reduce_unique step reduction]
    rfl
  · rintro rfl
    exact ⟨_, Prefix.core_step_iff.mpr ⟨_, reduction, rfl⟩, rfl⟩

private theorem selected_code (s : Store H) (outer : Execution.Runtime.Frame) (args : List Value) (value : BitVec 32) :
    let arms := entry.arms entry.inside.body.core (Graph.Op.emitList Graph.coreCodeSyntax entry.alternate)
    entry.coreSelected s outer args value =
      entry.site.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore,
        coreValues entry.site.cont.owner.initial ++ .plain (.block (Blocks.coreType entry.result)
          (if value = 0 then arms.2 else arms.1)) :: entry.tail.map Graph.coreEmit⟩ := by
  have site :
      entry.site.coreBody s outer args = entry.site.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore,
        coreValues entry.site.cont.owner.initial ++
          .plain (.block (Blocks.coreType entry.result) entry.inside.body.core) :: entry.tail.map Graph.coreEmit⟩ := by
    unfold GraphEntry.Entry.coreBody
    have rendered : expression entry.site.coreFunc.body = coreValues entry.site.cont.owner.initial ++
        .plain (.block (Blocks.coreType entry.result) entry.inside.body.core) :: entry.tail.map Graph.coreEmit := by
      change expression (_ ++ _) = _
      rw [expression_prefix]
      rw [site_body]
      change _ ++ .plain (.block (Blocks.coreType entry.result) entry.inside.body.core) ::
        expression (Graph.Op.emitList Graph.coreCodeSyntax entry.tail) = _
      rw [expression_tail entry.site.cont.owner]
    rw [rendered]
  have alternate :
      Graph.coreConfig s outer entry.site.cont.target (entry.alternatePhase args) =
        entry.site.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore,
          coreValues entry.site.cont.owner.initial ++
            .plain (.block (Blocks.coreType entry.result) (Graph.Op.emitList Graph.coreCodeSyntax entry.alternate)) ::
              entry.tail.map Graph.coreEmit⟩ := by
    rfl
  cases arm : entry.siteOnTrue <;> by_cases zero : value = (0#32) <;>
    simp [Entry.coreSelected, Entry.choosesSite, Entry.arms, arm, zero, site, alternate]

private theorem test_iff (dst : Config H) :
    Step P noHost (entry.coreTest s outer args value) dst ↔ dst = entry.coreSelected s outer args value := by
  let arms := entry.arms entry.inside.body.core (Graph.Op.emitList Graph.coreCodeSyntax entry.alternate)
  let code := coreValues (entry.site.cont.owner.initial ++ [.int .i32 value]) ++ .plain entry.coreIf :: entry.tail.map Graph.coreEmit
  have stays (out : List Admin) : ¬ LabelExit entry.site.cont.owner.declaration.results.length [] code out := by
    unfold code
    exact Computed.core_label_stays (head := .plain entry.coreIf)
      rfl (by simp [Entry.coreIf]) (by simp [Entry.coreIf])
      (by simp [Entry.coreIf, Admin.IsReturnCallRef]) (by simp [Entry.coreIf]) (by simp [Entry.coreIf])
  change Step P noHost (entry.site.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore, code⟩) dst ↔ _
  rw [Context.Resume.core_wrap_step_iff stays, selected_code]
  have raw (mid : Config H) := Computed.core_if_iff (P := P) (s := s) (f := (entry.site.frame args).toCore)
    (saved := entry.site.cont.owner.initial.map Value.toCore) (condition := value) (bt := Blocks.coreType entry.result) (thenBody := arms.1) (elseBody := arms.2)
    (rest := entry.tail.map Graph.coreEmit) (dst := mid)

  have exactStep (mid : Config H) :
      Step P noHost ⟨s, (entry.site.frame args).toCore, code⟩ mid ↔
        mid = ⟨s, (entry.site.frame args).toCore, coreValues entry.site.cont.owner.initial ++ .plain (.block (Blocks.coreType entry.result)
          (if value = 0 then arms.2 else arms.1)) :: entry.tail.map Graph.coreEmit⟩ := by
    have repr : (Value.int .i32 value).toCore = .num ⟨.int .i32, value⟩ := rfl
    simpa only [code, coreValues, List.map_append, List.map_singleton, repr, Entry.coreIf, arms] using raw mid
  simp only [exactStep, exists_eq_left, arms]

theorem front_exact (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance) (read : entry.Condition args value) :
    (coreSource s outer index args :: entry.coreFront s outer args value ++
      [entry.coreSelected s outer args value]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨invoke_iff ready allocated,
    List.isChain_cons_cons.mpr ⟨read_iff read, List.isChain_pair.mpr test_iff⟩⟩⟩
  intro dst
  exact Computed.core_direct_call_iff (s := s) (P := P) (stack := args) (tail := []) ready.resolves allocated

theorem alternate_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value) (select : entry.choosesSite value = false)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ coreSource s outer index args :: entry.coreFront s outer args value ∨
      ∃ phase, program.FrameRuns entry.site.cont.address (entry.alternatePhase args) phase ∧
        Graph.Admitted program entry.site.cont.owner phase ∧
        dst = Graph.coreConfig s outer entry.site.cont.target phase := by
  have path := front_exact (P := P) ready allocated read
  simp only [Entry.coreSelected, select, Bool.false_eq_true, ite_false] at path
  have checked := (Bool.and_eq_true_iff.mp (site_checked ready).source).1
  exact (Context.Resume.prefix_run_iff _ _ path).trans (or_congr Iff.rfl
    (Context.linked_runs checked ready.found (Graph.coreConfig s outer entry.site.cont.target) (Step P noHost)
      (fun h entered => Graph.core_entered_frame_step_iff checked links ready.found rfl h entered)
      (alternate_admitted ready) trivial))

private theorem enters_site (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true) :
    (coreSource s outer index args :: entry.coreFront s outer args value ++
      [entry.site.coreBody s outer args]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  simpa only [Entry.coreSelected, select, ite_true] using front_exact (P := P) ready allocated read

theorem site_run (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {call : Context.Invocation}
    (invoked : active.invocation program = some call) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args value) ++ entry.site.coreSitePath s outer args active (.resolved call.address) states ∨
      ∃ phase, Context.Resume.Runs program call entry.site.cont (.callee call.entered) phase ∧
        dst = entry.site.cont.coreConfig call s outer phase :=
  GraphEntry.core_run_via atSite .body (coreSource s outer index args) (entry.coreFront s outer args value)
    (enters_site ready allocated read select) tableAllocated targets links invoked

theorem lookup_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {stack : List Value} {active : Source.Activation}
    (atSite : entry.site.AtSite program tables outer index args states stack active)
    (tableAllocated : Source.Tables.CoreAllocated tables s)
    (targets : active.binding.site.CoreAllocated program s)
    {out : Outcome} (resolved : active.resolve program = some out) (trap : LookupTrap out) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ ((coreSource s outer index args :: entry.coreFront s outer args value) ++ entry.site.coreSitePath s outer args active out states).dropLast ∨
      ∃ phase, CleanupRuns (entry.site.coreTrapStart active out) phase ∧
        dst = entry.site.coreCleanup s outer active.caller phase :=
  GraphEntry.core_trap_run_via atSite .body (coreSource s outer index args) (entry.coreFront s outer args value)
    (enters_site ready allocated read select) tableAllocated targets resolved trap

theorem operand_trap (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.site.cont.address.value]? = some entry.coreInstance)
    (read : entry.Condition args value)
    (select : entry.choosesSite value = true)
    {states : List OperandState} {saved : List Value} {rest : List Prefix.Op}
    (trace : entry.site.OperandTrace args states (.trap saved rest)) {dst : Config H} :
    Steps P noHost (coreSource s outer index args) dst ↔
      dst ∈ (coreSource s outer index args :: entry.coreFront s outer args value) ++ entry.site.coreInside s outer args states ∨
      ∃ phase, CleanupRuns (entry.site.siteTrap Graph.coreEmit saved (entry.site.coreSiteCode rest)) phase ∧
        dst = entry.site.coreCleanup s outer (entry.site.frame args) phase :=
  GraphEntry.core_operand_trap_run_via .body (coreSource s outer index args) (entry.coreFront s outer args value)
    (enters_site ready allocated read select) trace

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Proofs.Core
