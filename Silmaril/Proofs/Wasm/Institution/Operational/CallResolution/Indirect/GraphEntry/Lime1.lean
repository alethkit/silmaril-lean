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

private theorem code (entry : Entry) :
    expression entry.limeFunc.body = values entry.cont.owner.initial ++
      entry.limeSiteCode entry.before := by
  let fn := entry.cont.owner
  have literals := Graph.lime_body_expression { fn with code := [] }
  have tail := Graph.lime_body_expression { fn with initial := [], code := entry.cont.code }
  change expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++ []) = values fn.initial ++ [] at literals
  change expression ([] ++ Graph.Op.emitList Graph.limeCodeSyntax entry.cont.code) = [] ++ entry.cont.code.map Graph.limeEmit at tail
  change expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++
    (entry.before.map (fun op => Graph.Op.emit Graph.limeCodeSyntax (.numeric op)) ++
      entry.op.limeInstr :: Graph.Op.emitList Graph.limeCodeSyntax entry.cont.code)) = _
  simp only [List.append_nil] at literals
  simp only [List.nil_append] at tail
  simp only [expression, List.map_append, List.map_cons, List.map_map] at literals tail ⊢
  rw [literals, tail]
  congr 1
  unfold Entry.limeSiteCode
  congr 1
  apply List.map_congr_left
  intro op _
  cases op <;> rfl

private theorem entry_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.cont.address.value]? = some entry.limeInstance) {dst : Config H} :
    Step CallFrame.limeNoHost (entry.limeInvoke s outer args) dst ↔
      dst = entry.limeOperands s outer args (entry.cont.owner.initial, entry.before) := by
  have count : args.length = entry.cont.owner.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length ready.typed)
  have enter := CallFrame.lime_invoke_wasm_exact (caller := outer) (dst := dst) allocated count
  change Step CallFrame.limeNoHost (entry.limeInvoke s outer args) dst ↔
    dst = ⟨s, outer, [.frame entry.cont.owner.declaration.results.length (entry.cont.owner.declaration.frame args)
      [.label entry.cont.owner.declaration.results.length [] (expression entry.limeFunc.body)]]⟩ at enter
  rw [code] at enter
  exact enter

private theorem operand_iff {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {ans : Prefix.Outcome} (move : Prefix.Reduce (entry.frame args).locals stack op ans)
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeOperands s outer args (stack, op :: rest)) dst ↔
      dst = match ans with
      | .values next => entry.limeOperands s outer args (next, rest)
      | .trap saved => entry.limeOperandResult s outer args (.trap saved rest) := by
  let tail := entry.limeSiteCode rest
  let exactStep (target : Config H) := Prefix.lime_step_iff (s := s) (f := entry.frame args)
    (stack := stack) (op := op) (tail := tail) (dst := target)
  constructor
  · intro wrapped
    rcases Computed.lime_body_step_cases wrapped with ⟨mid, inside, eq⟩ | ⟨out, leave, _⟩
    · obtain ⟨actual, reduced, midEq⟩ := (exactStep mid).mp inside
      cases Prefix.reduce_unique reduced move
      rw [eq, midEq]
      cases ans <;> rfl
    · exact False.elim (Computed.lime_label_stays
        (by cases op <;> rfl)
        (by cases op <;> simp [Prefix.emit, limeSyntax])
        (by cases op <;> simp [Prefix.emit, limeSyntax])
        (by cases op <;> simp [Prefix.emit, limeSyntax]) leave)
  · intro eq
    have inside := (exactStep _).mpr ⟨ans, move, rfl⟩
    rw [eq]
    cases ans <;> exact Step.frame (Step.label inside _ _) _ _

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
  refine List.isChain_cons_cons.mpr ⟨?_, (operand_chain trace).cons ?_⟩
  · intro dst
    exact Computed.lime_direct_call_iff (s := s) (stack := args) (tail := [])
      ready.resolves
  · intro b found dst
    rw [head] at found
    obtain rfl := Option.mem_some.mp found
    exact entry_iff ready allocated

theorem prefix_exact {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    (allocated : entry.LimeAllocated program tables active s) {out : Outcome}
    (resolved : active.resolve program = some out) :
    (entry.limePrefix s outer index args active out states).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  have prepare := prepare_spec ready
  have data := prepare.checked
  have before := operands_exact ready.checked allocated.entry ready.trace
  let site := entry.cont.limeWrap outer (active.limeSource s [] entry.cont.code)
  have lookup : [site, entry.cont.limeWrap outer (active.limeResolved s [] entry.cont.code out)].IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    List.isChain_pair.mpr (fun _ => Context.Resume.lime_resolution_allocated_iff data.site allocated.targets
      (Source.lime_table data allocated.tables) resolved)
  have same : entry.limeOperandResult s outer args (.values stack) = site := by
    simp only [Entry.limeOperandResult, Entry.limeOperands, Entry.limeSiteCode, site,
      Source.Activation.limeSource, Source.limeNest, List.foldr_nil, Indirect.limeSource,
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
      (entry.cont.limeWrap outer (active.limeResolved s [] entry.cont.code (.resolved call.address))) dst ↔
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
