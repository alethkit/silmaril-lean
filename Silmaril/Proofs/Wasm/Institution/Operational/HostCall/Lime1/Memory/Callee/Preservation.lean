module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

open Execution.Runtime (Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

theorem get_typed {callee : MemoryTarget} {args stack : List Value} {i : LocalIdx}
    {ops : List Graph.Memory32.Op} (argsTyped : args.map Value.type = callee.fn.declaration.params)
    (typed : callee.fn.WellTyped stack (.ranked (.numeric (.get i)) :: ops)) :
    ∃ v, (callee.fn.declaration.frame args).locals[i.toNat]? = some v ∧
      callee.fn.WellTyped (stack ++ [v]) ops := by
  have locals : (callee.fn.declaration.frame args).locals.map Value.type =
      callee.fn.declaration.params ++ callee.fn.declaration.locals := by
    simp [Declaration.frame, List.map_map, Function.comp_def, Value.zero, argsTyped]
  unfold Graph.Memory32.Function.WellTyped Graph.Memory32.Function.checkCode at typed
  simp only [Graph.Memory32.Function.checkRegion, Graph.Memory32.Function.checkRegionOp,
    Graph.checkOp, Prefix.checkOp] at typed
  rw [← locals, List.getElem?_map] at typed
  cases found : (callee.fn.declaration.frame args).locals[i.toNat]? with
  | none => simp [found] at typed
  | some v =>
    exact ⟨v, rfl, by
      simpa [found, Graph.Memory32.Function.WellTyped, Graph.Memory32.Function.checkCode,
        Prefix.stackTypes, List.reverse_append] using typed⟩

theorem typed_nil {callee : MemoryTarget} {stack : List Value} (typed : callee.fn.WellTyped stack []) :
    resultTyped callee (.values stack) := by
  simpa [Graph.Memory32.Function.WellTyped, Graph.Memory32.Function.checkCode,
    Graph.Memory32.Function.checkRegion, Prefix.stackTypes, resultTyped] using typed

private theorem resume_typed {fn : Graph.Memory32.Function} {saved operands : List Value}
    {params results : List NumType} {rest : List Graph.Memory32.Op}
    (arguments : operands.map Value.type = params)
    (resume : fn.checkCode (results.reverse ++ (Prefix.stackTypes (saved ++ operands)).drop params.length) rest = true)
    (vs : List Value) (typed : vs.map Value.type = results) : fn.WellTyped (saved ++ vs) rest := by
  have count : params.reverse.length = params.length := List.length_reverse
  have kept : (params.reverse ++ Prefix.stackTypes saved).drop params.length = Prefix.stackTypes saved := by
    rw [← count, List.drop_left]
  simp only [Prefix.stackTypes] at kept
  simpa only [Graph.Memory32.Function.WellTyped, Prefix.stackTypes, List.map_append,
    List.reverse_append, arguments, typed, kept] using resume

theorem call_typed {callee : MemoryTarget} {stack : List Value} {target : CallTarget}
    {ops : List Graph.Memory32.Op} (typed : callee.fn.WellTyped stack (.ranked (.call target) :: ops)) :
    ∃ saved operands, stack = saved ++ operands ∧ operands.map Value.type = target.declaration.params ∧
      target ∈ callee.fn.targets ∧
      ∀ vs : List Value, vs.map Value.type = target.declaration.results → callee.fn.WellTyped (saved ++ vs) ops := by
  change (decide (target ∈ callee.fn.targets ∧
    (Prefix.stackTypes stack).take target.declaration.params.length = target.declaration.params.reverse) &&
    callee.fn.checkCode (target.declaration.results.reverse ++
      (Prefix.stackTypes stack).drop target.declaration.params.length) ops) = true at typed
  obtain ⟨guard, resume⟩ := Bool.and_eq_true_iff.mp typed
  obtain ⟨used, suffix⟩ := of_decide_eq_true guard
  obtain ⟨saved, operands, rfl, arguments⟩ := Graph.SuffixTyped.split suffix
  exact ⟨saved, operands, rfl, arguments, used, resume_typed arguments resume⟩

private theorem direct_resume {callee : MemoryTarget} {saved operands : List Value} {target : CallTarget}
    {rest : List Graph.Memory32.Op} (typed : operands.map Value.type = target.declaration.params)
    (checked : callee.fn.WellTyped (saved ++ operands) (.ranked (.call target) :: rest)) :
    ∀ vs : List Value, vs.map Value.type = target.declaration.results → callee.fn.WellTyped (saved ++ vs) rest := by
  obtain ⟨kept, used, split, usedTyped, _, resume⟩ := call_typed checked
  have count : used.length = operands.length := by
    simpa using congrArg List.length (usedTyped.trans typed.symm)
  obtain ⟨rfl, _⟩ := List.append_inj' split count.symm
  exact resume

theorem indirect_typed {callee : MemoryTarget} {stack : List Value} {index : TypeIdx}
    {signature : Wasm.V1.FuncType} {rest : List Graph.Memory32.Op}
    (typed : callee.fn.WellTyped stack (.callIndirect index signature :: rest)) :
    ∃ (saved operands : List Value) (selector : BitVec 32), stack = (saved ++ operands) ++ [Value.int .i32 selector] ∧
      operands.map Value.type = signature.params ∧
      ∀ vs : List Value, vs.map Value.type = signature.results → callee.fn.WellTyped (saved ++ vs) rest := by
  obtain ⟨stack, selector, rfl, suffix, resume⟩ := Graph.Memory32.Function.indirect_typed typed
  obtain ⟨saved, operands, rfl, arguments⟩ := Graph.SuffixTyped.split suffix
  exact ⟨saved, operands, selector, rfl, arguments, resume_typed arguments resume⟩

private theorem indirect_resume {callee : MemoryTarget} {saved operands : List Value} {index : TypeIdx}
    {signature : Wasm.V1.FuncType} {selector : BitVec 32} {rest : List Graph.Memory32.Op}
    (typed : operands.map Value.type = signature.params)
    (checked : callee.fn.WellTyped ((saved ++ operands) ++ [Value.int .i32 selector])
      (.callIndirect index signature :: rest)) :
    ∀ vs : List Value, vs.map Value.type = signature.results → callee.fn.WellTyped (saved ++ vs) rest := by
  obtain ⟨kept, used, _, split, usedTyped, resume⟩ := indirect_typed checked
  obtain ⟨split, _⟩ := List.append_inj' split (by simp)
  have count : used.length = operands.length := by
    simpa using congrArg List.length (usedTyped.trans typed.symm)
  obtain ⟨rfl, _⟩ := List.append_inj' split count.symm
  exact resume

theorem after_child_render {H : Type} (parent child : MemoryTarget) (args saved : List Value)
    (rest : List Graph.Memory32.Op) (phase : Phase H) :
    render parent (afterChild args saved child rest phase) =
      [.frame parent.fn.declaration.results.length (parent.fn.declaration.frame args)
        [.label parent.fn.declaration.results.length [] (values saved ++ render child phase ++ code rest)]] := by
  cases phase <;> try rfl
  case done out =>
    cases out <;>
      simp [afterChild, render, result, values_append, List.append_assoc]

private theorem tail_supported {enabled : Bool} {op : Graph.Memory32.Op} {ops : List Graph.Memory32.Op}
    (checked : (op :: ops).all (MemoryTarget.supportedOp enabled) = true) :
    ops.all (MemoryTarget.supportedOp enabled) = true := by
  exact List.all_eq_true.mpr (fun a member => List.all_eq_true.mp checked a (List.mem_cons_of_mem _ member))

theorem ready_step {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {host : HostSemantics H} {site : IndirectSite} {bytes written : ByteArray} {phase next : Phase H}
    (linked : site.MemoryLinked mem host .recursive) (registered : site.memoryLookup callee.address = some callee.fn)
    (move : Edge mem host site callee bytes phase written next)
    (ready : Ready mem host site callee phase) : Ready mem host site callee next := by
  induction move with
  | enter =>
    have checked := linked.checked _ registered
    exact ⟨ready, checked.supported, checked.body, fun _ member => member⟩
  | get found =>
    obtain ⟨v, lookup, typed⟩ := get_typed ready.1 ready.2.2.1
    rw [found] at lookup
    cases lookup
    exact ⟨ready.1, tail_supported ready.2.1, typed, fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)⟩
  | load _ =>
    obtain ⟨kept, address, split, typed⟩ := Graph.Memory32.Function.load_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed _, fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)⟩
  | store _ =>
    obtain ⟨kept, address, operand, split, typed⟩ := Graph.Memory32.Function.store_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed, fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)⟩
  | size =>
    exact ⟨ready.1, tail_supported ready.2.1, Graph.Memory32.Function.size_typed ready.2.2.1 _,
      fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)⟩
  | grow _ _ | growFail =>
    obtain ⟨kept, delta, split, typed⟩ := Graph.Memory32.Function.grow_typed ready.2.2.1
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed _, fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)⟩
  | @call callee child bytes args saved operands target rest link typed =>
    have resume := direct_resume typed ready.2.2.1
    refine ⟨ready.1, link.registered, link.allocated, by simp, ?_,
      tail_supported ready.2.1, (fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)), ?_⟩
    · simpa only [Ready, link.declaration] using typed
    · simpa only [link.declaration] using resume
  | callHost link typed =>
    exact ⟨ready.1, link.allocated, typed, link.contract, tail_supported ready.2.1,
      (fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)), direct_resume typed ready.2.2.1⟩
  | @callIndirect callee child bytes args saved operands index signature selector rest lookup typed =>
    have resume := indirect_resume typed ready.2.2.1
    cases lookup with
    | memory _ found allocated signatureEq =>
      have params := congrArg (fun (ty : Wasm.Lime1.FuncType) => ty.params) signatureEq
      have results := congrArg (fun (ty : Wasm.Lime1.FuncType) => ty.results) signatureEq
      refine ⟨ready.1, found, allocated, by simp, ?_, tail_supported ready.2.1,
        (fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)), ?_⟩
      · exact typed.trans params.symm
      · exact fun vs typed => resume vs (typed.trans results)
  | @callIndirectHost callee target bytes args saved operands index signature selector rest lookup typed =>
    have resume := indirect_resume typed ready.2.2.1
    cases lookup with
    | @host address hostCode entry allocated =>
      have link := linked.indirect callee registered index signature (ready.2.2.2 _ (by simp))
      obtain ⟨fn, found, contract⟩ := link.entries address (List.mem_of_getElem? entry)
      change base.funcs[address.value]? = some (.host ⟨signature.params, signature.results⟩ hostCode)
        at allocated
      rw [allocated] at found
      cases found
      exact ⟨ready.1, allocated, typed, contract rfl, tail_supported ready.2.1,
        (fun op member => ready.2.2.2 op (List.mem_cons_of_mem _ member)), resume⟩
  | hostReturned _ typed _ =>
    obtain ⟨argsTyped, _, _, _, supported, inCode, resume⟩ := ready
    exact ⟨argsTyped, supported, resume _ typed, inCode⟩
  | hostTrapped => exact ready.1
  | hostDiverged => exact ready
  | @child callee child bytes written args saved phase next rest move ih =>
    obtain ⟨argsTyped, found, allocated, _, childReady, supported, inCode, resume⟩ := ready
    have after := ih found childReady
    cases next <;> try exact ⟨argsTyped, found, allocated, by simp, after, supported, inCode, resume⟩
    case done out =>
      cases out with
      | trap => exact argsTyped
      | values vs => exact ⟨argsTyped, supported, resume vs after, inCode⟩
  | loadTrap | storeTrap | indirectTrap => exact ready.1
  | erase => exact ready
  | labelDone => exact ⟨ready.1, typed_nil ready.2.2.1⟩
  | labelTrap => exact ⟨ready, trivial⟩
  | frameDone => exact ready.2

theorem live_step {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {host : HostSemantics H} {site : IndirectSite} {bytes written : ByteArray} {phase next : Phase H}
    (move : Edge mem host site callee bytes phase written next) (live : mem.Live bytes) : mem.Live written := by
  induction move with
  | child _ ih => exact ih live
  | hostReturned nextLive _ _ | hostTrapped nextLive _ => exact nextLive
  | store write => exact mem.live_same_size live (MemoryWrite.closed_at write)
  | grow enabled edge => exact mem.live_grow enabled live edge
  | _ => exact live

theorem extent_mono {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {site : IndirectSite} {bytes written : ByteArray} {phase next : Phase H}
    (move : Edge mem Execution.Runtime.noHostCalls site callee bytes phase written next) : bytes.size ≤ written.size := by
  induction move with
  | child _ ih => exact ih
  | hostReturned _ _ answer | hostTrapped _ answer => exact answer.elim
  | store write => exact Nat.le_of_eq (MemoryWrite.closed_at write).symm
  | grow _ edge =>
    rw [MemoryGrow.grown_bytes edge]
    simp only [Memory32.current, ByteArray.size_append]
    exact Nat.le_add_right _ _
  | _ => exact Nat.le_refl _

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs
