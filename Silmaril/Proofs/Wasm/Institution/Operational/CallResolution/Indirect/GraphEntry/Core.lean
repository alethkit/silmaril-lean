module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
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

private theorem code (entry : Entry) :
    expression entry.coreFunc.body = coreValues entry.cont.owner.initial ++
      entry.coreSiteCode entry.before := by
  let fn := entry.cont.owner
  have values := Graph.core_body_expression { fn with code := [] }
  have tail := Graph.core_body_expression { fn with initial := [], code := entry.cont.code }
  change expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++ []) = coreValues fn.initial ++ [] at values
  change expression ([] ++ Graph.Op.emitList Graph.coreCodeSyntax entry.cont.code) = [] ++ entry.cont.code.map Graph.coreEmit at tail
  change expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++
    (entry.before.map (fun op => Graph.Op.emit Graph.coreCodeSyntax (.numeric op)) ++
      entry.op.coreInstr :: Graph.Op.emitList Graph.coreCodeSyntax entry.cont.code)) = _
  simp only [List.append_nil] at values
  simp only [List.nil_append] at tail
  simp only [expression, List.map_append, List.map_cons, List.map_map] at values tail ⊢
  rw [values, tail]
  congr 1
  unfold Entry.coreSiteCode
  congr 1
  apply List.map_congr_left
  intro op _
  cases op <;> rfl

private theorem entry_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.coreInstance) {dst : Config H} :
    Step P noHost (entry.coreInvoke s outer args) dst ↔ dst = entry.coreOperands s outer args (entry.cont.owner.initial, entry.before) := by
  have enter := Sequence.wasm_entry_iff (P := P) (caller := outer) (dst := dst) allocated ready.typed
  have frame := Sequence.core_frame_forCall entry.cont.owner.declaration.module args entry.cont.owner.declaration.locals
  change Core.Frame.forCall entry.cont.owner.declaration.module.toCore (args.map Value.toCore) entry.coreFunc.locals =
    (entry.cont.owner.declaration.frame args).toCore at frame
  rw [frame, code] at enter
  exact enter

private theorem operand_iff {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {ans : Prefix.Outcome} (move : Prefix.Reduce (entry.frame args).locals stack op ans)
    (dst : Config H) :
    Step P noHost (entry.coreOperands s outer args (stack, op :: rest)) dst ↔
      dst = match ans with
      | .values next => entry.coreOperands s outer args (next, rest)
      | .trap saved => entry.coreOperandResult s outer args (.trap saved rest) := by
  let tail := entry.coreSiteCode rest
  let exactStep (target : Config H) := Prefix.core_step_iff (P := P) (s := s) (f := entry.frame args)
    (stack := stack) (op := op) (tail := tail) (dst := target)
  constructor
  · intro wrapped
    rcases Computed.core_body_step_cases wrapped with ⟨mid, inside, eq⟩ | ⟨out, leave, _⟩
    · obtain ⟨actual, reduced, midEq⟩ := (exactStep mid).mp inside
      cases Prefix.reduce_unique reduced move
      rw [eq, midEq]
      cases ans <;> rfl
    · exact False.elim (Computed.core_label_stays
        (by cases op <;> rfl)
        (by cases op <;> simp [Prefix.emit, coreSyntax])
        (by cases op <;> simp [Prefix.emit, coreSyntax]) (by cases op <;> simp [Prefix.emit, coreSyntax, Core.Admin.IsReturnCallRef])
        (by cases op <;> simp [Prefix.emit, coreSyntax])
        (by cases op <;> simp [Prefix.emit, coreSyntax]) leave)
  · intro eq
    have inside := (exactStep _).mpr ⟨ans, move, rfl⟩
    rw [eq]
    cases ans <;> exact Step.ctxtFrame (Step.ctxtLabel inside)

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
  refine List.isChain_cons_cons.mpr ⟨?_, (operand_chain trace).cons ?_⟩
  · intro dst
    exact Computed.core_direct_call_iff (s := s) (P := P) (stack := args) (tail := [])
      ready.resolves allocated
  · intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact entry_iff ready allocated

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
      Source.Activation.coreConfig, Source.coreNest, List.foldr_nil, Indirect.coreConfig, Site.coreCode,
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
