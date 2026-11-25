module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Proofs

open Execution
open Execution.Runtime (Frame FuncAddr ModuleInst Value)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

private theorem bind_checked {op : Op} {program : Graph.Program} {tables : Tables}
    {caller : ModuleInst} {bound : Binding} (prepared : op.bind program tables caller = some bound) :
    caller.tables[tableIndex.toNat]? = some bound.address ∧
      tables[bound.address.value]? = some bound.site.table ∧
      bound.site.typeIndex = op.typeIndex ∧ bound.site.signature = op.signature ∧
      bound.site.check program ⟨[], caller⟩ = true := by
  cases address : caller.tables[tableIndex.toNat]? with
  | none => simp [Op.bind, address] at prepared
  | some addr =>
    cases located : tables[addr.value]? with
    | none => simp [Op.bind, address, located] at prepared
    | some table =>
      let site : Site := ⟨table, op.typeIndex, op.signature⟩
      by_cases checked : site.check program ⟨[], caller⟩ = true
      · have eq : Binding.mk addr site = bound := by
          simpa [Op.bind, address, located, site, checked] using prepared
        subst bound
        exact ⟨rfl, located, rfl, rfl, checked⟩
      · simp [Op.bind, address, located, site, checked] at prepared

theorem split_spec {op : Op} {stack : List Value} {operands : Operands} (split : op.split stack = some operands) :
    stack = operands.saved ++ operands.args ++ [Value.int .i32 operands.selector] ∧
      operands.args.map Value.type = op.signature.params := by
  cases reverse : stack.reverse with
  | nil => simp [Op.split, reverse] at split
  | cons value tail =>
    rcases value with ⟨type, bits⟩
    cases type with
    | float t => simp [Op.split, reverse] at split
    | int t =>
      cases t with
      | i64 => simp [Op.split, reverse] at split
      | i32 =>
        let args := (tail.take op.signature.params.length).reverse
        by_cases typed : (tail.take op.signature.params.length).reverse.map Value.type = op.signature.params
        · have parts : Operands.mk (tail.drop op.signature.params.length).reverse args bits = operands := by
            simpa only [Op.split, reverse, ite_eq_left typed, Option.some.injEq] using split
          subst operands
          refine ⟨?_, typed⟩
          have reconstructed := congrArg List.reverse reverse
          rw [List.reverse_reverse, List.reverse_cons] at reconstructed
          rw [reconstructed, ← List.reverse_append, List.take_append_drop]
          rfl
        · simp only [Op.split, reverse, ite_eq_right typed, reduceCtorEq] at split

theorem prepare_spec {op : Op} {program : Graph.Program} {tables : Tables}
    {caller : Frame} {stack : List Value} {active : Activation}
    (prepared : op.prepare program tables caller stack = some active) :
    op.Prepared program tables caller stack active := by
  cases binding : op.bind program tables caller.module with
  | none => simp [Op.prepare, binding] at prepared
  | some bound =>
    cases split : op.split stack with
    | none => simp [Op.prepare, binding, split] at prepared
    | some operands =>
      have exactState : Activation.mk caller bound operands = active := by
        simpa [Op.prepare, binding, split] using prepared
      subst active
      obtain ⟨addressed, table, index, signature, checked⟩ := bind_checked binding
      obtain ⟨stackEq, typed⟩ := split_spec split
      exact ⟨rfl, ⟨addressed, table, checked, typed.trans (congrArg V1.FuncType.params signature.symm)⟩, index, signature, stackEq⟩

theorem check_stack {op : Op} {types : List V1.FuncType} {saved args : List Value} {selector : BitVec 32}
    (typeFound : types[op.typeIndex.toNat]? = some op.signature)
    (typed : args.map Value.type = op.signature.params) :
    op.checkStack types (Prefix.stackTypes (saved ++ args ++ [Value.int .i32 selector])) =
      some (op.signature.results.reverse ++ Prefix.stackTypes saved) := by
  simp only [Op.checkStack, Prefix.stackTypes, List.map_append, List.reverse_append, List.reverse_singleton,
    List.map_singleton, List.singleton_append, Value.int, typed, typeFound, true_and]
  have n : op.signature.params.reverse.length = op.signature.params.length := List.length_reverse
  rw [← n, List.take_left, List.drop_left, ite_eq_left rfl]

theorem prepare_of_check {op : Op} {program : Graph.Program} {tables : Tables} {caller : Frame}
    {stack : List Value} {next : List NumType}
    (binding : (op.bind program tables caller.module).isSome = true)
    (typed : op.checkStack caller.module.types (Prefix.stackTypes stack) = some next) :
    ∃ active, op.prepare program tables caller stack = some active := by
  obtain ⟨bound, boundEq⟩ := Option.isSome_iff_exists.mp binding
  have stackTypes : Prefix.stackTypes stack = stack.reverse.map Value.type := List.map_reverse.symm
  rw [stackTypes] at typed
  cases reversed : stack.reverse with
  | nil => simp [Op.checkStack, reversed] at typed
  | cons value rest =>
    rcases value with ⟨type, bits⟩
    cases type with
    | float t => simp [Op.checkStack, reversed] at typed
    | int t =>
      cases t with
      | i64 => simp [Op.checkStack, reversed] at typed
      | i32 =>
        have suffix : (rest.map Value.type).take op.signature.params.length = op.signature.params.reverse := by
          by_contra mismatch
          simp [Op.checkStack, reversed, mismatch] at typed
        have args : (rest.take op.signature.params.length).reverse.map Value.type = op.signature.params := by
          rw [List.map_reverse, List.map_take, suffix, List.reverse_reverse]
        refine ⟨⟨caller, bound, ⟨(rest.drop op.signature.params.length).reverse,
          (rest.take op.signature.params.length).reverse, bits⟩⟩, ?_⟩
        simp [Op.prepare, boundEq, Op.split, reversed, args]

theorem region_binding {body : Body} {program : Graph.Program} {tables : Tables}
    {fn : Graph.Function} {fallthrough : List NumType} {enclosing : Graph.EnclosingLabels}
    {stack : List NumType}
    (checked : body.checkRegion program tables fn fallthrough enclosing stack = true) :
    (body.operation.bind program tables fn.declaration.module).isSome = true := by
  induction body generalizing fallthrough enclosing stack with
  | indirect => exact (Bool.and_eq_true_iff.mp checked).1
  | block _ _ _ ih => exact ih (Bool.and_eq_true_iff.mp checked).1

theorem core_table {H : Type} {program : Graph.Program} {tables : Tables} {active : Activation}
    {s : Core.Store H} (checked : active.Checked program tables) (allocated : Tables.CoreAllocated tables s) :
    s.table? active.caller.toCore tableIndex =
      some (active.binding.address.value, active.binding.site.table.toCore) := by
  simp [Core.Store.table?, Runtime.Frame.toCore, Runtime.ModuleInst.toCore, List.getElem?_map,
    checked.addressed, allocated _ _ checked.table]

theorem lime_table {H : Type} {program : Graph.Program} {tables : Tables} {active : Activation}
    {s : Wasm.Lime1.Execution.Store H} (checked : active.Checked program tables)
    (allocated : Tables.LimeAllocated tables s) :
    Wasm.Lime1.Execution.frameTable s active.caller = some active.binding.site.table := by
  have slot : active.caller.module.tables[0]? = some active.binding.address := checked.addressed
  simp [Wasm.Lime1.Execution.frameTable, slot, allocated _ _ checked.table]

theorem invocation_fields {active : Activation} {program : Graph.Program} {call : Context.Invocation}
    (invoked : active.invocation program = some call) :
    ∃ address callee, active.resolve program = some (.resolved address) ∧
      program.lookup address = some callee ∧
      call = ⟨active.binding.site, active.caller, active.operands.selector, active.operands.saved,
        active.operands.args, address, callee⟩ := by
  cases result : active.resolve program with
  | none => simp [Activation.invocation, result] at invoked
  | some out =>
    cases out with
    | bounds | null | mismatch => simp [Activation.invocation, result] at invoked
    | resolved addr =>
      cases fn : program.lookup addr with
      | none => simp [Activation.invocation, result, fn] at invoked
      | some callee =>
        exact ⟨addr, callee, rfl, fn, by simpa [Activation.invocation, result, fn, eq_comm] using invoked⟩

theorem invocation_checked {active : Activation} {program : Graph.Program} {tables : Tables}
    {call : Context.Invocation} (checked : active.Checked program tables) (graph : program.checkDirect = true)
    (invoked : active.invocation program = some call) : call.Checked program := by
  obtain ⟨address, callee, resolved, found, rfl⟩ := invocation_fields invoked
  exact ⟨graph, checked.site, resolved, found, checked.args⟩

theorem invocation_core_table {H : Type} {active : Activation} {program : Graph.Program} {tables : Tables}
    {s : Core.Store H} {call : Context.Invocation} (checked : active.Checked program tables)
    (allocated : Tables.CoreAllocated tables s) (invoked : active.invocation program = some call) :
    s.table? call.caller.toCore tableIndex = some (active.binding.address.value, call.site.table.toCore) := by
  obtain ⟨_, _, _, _, rfl⟩ := invocation_fields invoked
  exact core_table checked allocated

theorem invocation_lime_table {H : Type} {active : Activation} {program : Graph.Program} {tables : Tables}
    {s : Wasm.Lime1.Execution.Store H} {call : Context.Invocation} (checked : active.Checked program tables)
    (allocated : Tables.LimeAllocated tables s) (invoked : active.invocation program = some call) :
    Wasm.Lime1.Execution.frameTable s call.caller = some call.site.table := by
  obtain ⟨_, _, _, _, rfl⟩ := invocation_fields invoked
  exact lime_table checked allocated

theorem resume_checked {op : Op} {program : Graph.Program} {tables : Tables} {caller : Frame}
    {stack : List Value} {active : Activation} {call : Context.Invocation} {cont : Context.Resume.Continuation}
    (prepared : op.Prepared program tables caller stack active) (invoked : active.invocation program = some call)
    (found : program.lookup cont.address = some cont.owner) (moduleEq : caller.module = cont.owner.declaration.module)
    (localsTyped : caller.locals.map Value.type = cont.owner.localTypes)
    (tail : op.checkTail cont.owner cont.owner.declaration.results [] (Prefix.stackTypes stack) cont.code = true) :
    cont.Checked program call.caller call.saved call.site.signature.results := by
  obtain ⟨_, _, _, _, rfl⟩ := invocation_fields invoked
  have typeFound := of_decide_eq_true (Bool.and_eq_true_iff.mp prepared.checked.site).1
  rw [prepared.caller_eq, moduleEq, prepared.typeIndex_eq, prepared.signature_eq] at typeFound
  have stackCheck := check_stack (selector := active.operands.selector) (saved := active.operands.saved)
    typeFound (prepared.checked.args.trans (congrArg V1.FuncType.params prepared.signature_eq))
  rw [Op.checkTail, prepared.stack_eq, stackCheck] at tail
  exact ⟨found, (congrArg Frame.module prepared.caller_eq).trans moduleEq, by simpa only [prepared.caller_eq] using localsTyped,
    by simpa [prepared.signature_eq] using tail⟩

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Proofs
