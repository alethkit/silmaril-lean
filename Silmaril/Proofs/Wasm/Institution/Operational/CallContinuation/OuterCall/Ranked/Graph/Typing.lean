module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr Value)
open Computed

private theorem lookup_mem {program : Program} {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) : some fn ∈ program.functions := by
  cases slot : program.functions[address.value]? with
  | none => simp [Program.lookup, slot] at found
  | some data =>
    have same : data = some fn := by simpa [Program.lookup, slot] using found
    exact same ▸ List.mem_of_getElem? slot

theorem check_function {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.check = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 (some fn) (lookup_mem found)

theorem scalar_result {program : Program} (checked : program.checkV1 = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 := by
  have scalar := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 (some fn) (lookup_mem found)
  simpa only [Option.map_some, Option.getD_some, decide_eq_true_eq] using scalar

theorem linked_target {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address := by
  have member : some fn.entry ∈ program.table.entries :=
    List.mem_map_of_mem (f := Option.map Function.entry) (lookup_mem found)
  obtain ⟨callee, lookup, resolves, declared, _⟩ :=
    (Table.check_iff program.table).mp (Program.rankCheck checked) fn.entry member target used
  rw [lookup_table] at lookup
  cases h : program.lookup target.address with
  | none => simp [h] at lookup
  | some body =>
    have same : body.entry = callee := by simpa [h] using lookup
    exact ⟨body, rfl, (congrArg Entry.declaration same).trans declared, resolves⟩

private theorem stack_types_append (below above : List Value) :
    Prefix.stackTypes (below ++ above) = Prefix.stackTypes above ++ Prefix.stackTypes below := by
  simp [Prefix.stackTypes]

private theorem args_check {fn : Function} {target : CallTarget} {saved operands : List Value} {rest : List Op}
    (count : operands.length = target.declaration.params.length)
    (typed : fn.WellTyped (saved ++ operands) (.call target :: rest)) :
    operands.map Value.type = target.declaration.params ∧ fn.ResumeTyped saved target rest := by
  have length : operands.length = (Prefix.stackTypes operands).length := by simp [Prefix.stackTypes]
  unfold Function.WellTyped at typed
  simp only [checkCode, Bool.and_eq_true_iff, decide_eq_true_eq, stack_types_append, ← count, length,
    List.take_left, List.drop_left] at typed
  exact ⟨List.reverse_inj.mp typed.1.2, typed.2⟩

private theorem init_local_types {fn : Function} {args : List Value} (typed : args.map Value.type = fn.declaration.params) :
    (fn.declaration.frame args).locals.map Value.type = fn.localTypes := by
  simp [Declaration.frame, Function.localTypes, List.map_map, Function.comp_def, Value.zero, typed]

private theorem result_of_nil {fn : Function} {stack : List Value} (typed : fn.WellTyped stack []) :
    fn.ResultTyped (.values stack) := by
  simpa [Function.WellTyped, Function.ResultTyped, checkCode, Prefix.stackTypes] using typed

private theorem return_of_code {fn : Function} {stack : List Value} {rest : List Op}
    (typed : fn.WellTyped stack (.return_ :: rest)) : fn.ReturnTyped stack := by
  simpa [Function.WellTyped, Function.ReturnTyped, checkCode] using typed

private theorem return_result {fn : Function} {extra results : List Value}
    (typed : fn.ReturnTyped (extra ++ results)) (arity : results.length = fn.declaration.results.length) :
    fn.ResultTyped (.values results) := by
  have length : (Prefix.stackTypes results).length = fn.declaration.results.length := by
    simpa [Prefix.stackTypes] using arity
  unfold Function.ReturnTyped at typed
  rw [stack_types_append, ← length, List.take_left] at typed
  exact List.reverse_inj.mp typed

private theorem numeric_preserves {fn : Function} {locals stack next : List Value} {op : Prefix.Op} {rest : List Op}
    (typed : locals.map Value.type = fn.localTypes)
    (step : Prefix.Reduce locals stack op (.values next))
    (body : fn.WellTyped stack (.numeric op :: rest)) : fn.WellTyped next rest := by
  have head := Prefix.checkOp_result step
  rw [typed] at head
  simpa [Function.WellTyped, checkCode, head] using body

private theorem set_preserves {fn : Function} {locals next saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
    (typed : locals.map Value.type = fn.localTypes)
    (write : Locals.Edge ⟨locals, [.value v, .set i]⟩ ⟨next, []⟩)
    (body : fn.WellTyped (saved ++ [v]) (.set i :: rest)) :
    next.map Value.type = fn.localTypes ∧ fn.WellTyped saved rest := by
  by_cases fits : fn.localTypes[i.toNat]? = some v.type
  · have localGuard : Locals.Admitted fn.localTypes [] ⟨locals, [.value v, .set i]⟩ :=
      ⟨typed, by simp [Locals.check, fits]⟩
    exact ⟨(Locals.closed localGuard write).1,
      by simpa [Function.WellTyped, checkCode, Prefix.stackTypes, Locals.check, fits] using body⟩
  · simp [Function.WellTyped, checkCode, Prefix.stackTypes, Locals.check, fits] at body

private theorem tee_preserves {fn : Function} {saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
    (body : fn.WellTyped (saved ++ [v]) (.tee i :: rest)) :
    fn.WellTyped (saved ++ [v, v]) (.set i :: rest) := by
  by_cases fits : fn.localTypes[i.toNat]? = some v.type <;>
    simp_all [Function.WellTyped, checkCode, Prefix.stackTypes, Locals.check]

theorem admitted_step {program : Program} (checked : program.check = true) (address : FuncAddr) :
    ∀ {fn a b}, program.lookup address = some fn → Admitted program fn a →
      program.Edge checked address a b → Admitted program fn b := by
  induction address using (program.table.wellFounded (Program.rankCheck checked)).induction with
  | h address ih =>
    intro fn a b found ready move
    have step := (edge_iff checked found).mp move
    cases step with
    | resolve args => cases ready with | call typed => exact .invoke typed
    | enter args typed => exact .running (init_local_types typed) (check_function checked found)
    | numeric step =>
      cases ready with
      | running typed body =>
        cases step
        · exact .running typed (numeric_preserves typed (.get ‹_›) body)
        · exact .running typed (numeric_preserves typed (.bin ‹_›) body)
        · exact .trapped typed
    | localSet write =>
      cases ready with
      | running typed body =>
        obtain ⟨nextTyped, restTyped⟩ := set_preserves typed write body
        exact .running nextTyped restTyped
    | localTee _ =>
      cases ready with
      | running typed body => exact .running typed (tee_preserves body)
    | unreachable args stack rest => cases ready with | running typed _ => exact .trapped typed
    | dispatch args saved operands target rest used count =>
      cases ready with
      | running typed body =>
        obtain ⟨callee, calleeFound, declared, _⟩ := linked_target checked found used
        obtain ⟨callArgs, resume⟩ := args_check count body
        exact .active typed used calleeFound declared trivial (.invoke (callArgs.trans (congrArg Declaration.params declared).symm)) resume
    | child args saved target rest used live step =>
      cases ready with
      | active typed _ childFound declared _ childReady resume =>
        have next := ih target.address (target_resolved checked found used) childFound childReady step
        cases next with
        | call newArgs =>
          exact (not_call step _ rfl).elim
        | invoke newArgs => exact .active typed used childFound declared trivial (.invoke newArgs) resume
        | running newArgs body => exact .active typed used childFound declared trivial (.running newArgs body) resume
        | active newArgs edge alloc same live ready body =>
          exact .active typed used childFound declared trivial (.active newArgs edge alloc same live ready body) resume
        | trapped newArgs => exact .active typed used childFound declared trivial (.trapped newArgs) resume
        | returning newArgs out => exact .active typed used childFound declared trivial (.returning newArgs out) resume
        | exit newArgs out => exact .active typed used childFound declared trivial (.exit newArgs out) resume
        | @done _ result out =>
          cases result with
          | trap => exact .trapped typed
          | values stack =>
            have values : stack.map Value.type = target.declaration.results :=
              out.trans (congrArg Declaration.results declared)
            exact .running typed (by simpa [Function.WellTyped, Function.ResumeTyped, stack_types_append,
              Prefix.stackTypes, values] using resume)
    | discard cut => cases ready with | trapped typed => exact .trapped typed
    | returnLabel _ _ _ =>
      cases ready with | running typed body => exact .returning typed (return_of_code body)
    | returnFrame _ _ _ arity =>
      cases ready with | returning _ out => exact .done (return_result out arity)
    | leaveValues args stack =>
      cases ready with | running typed body => exact .exit typed (result_of_nil body)
    | leaveTrap args => cases ready with | trapped typed => exact .exit typed trivial
    | leaveFrame args result typed => exact .done typed

theorem nesting_of_admitted {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {phase : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn phase) : program.table.Nesting (phase.frames address) := by
  induction ready generalizing address with
  | @active fn args saved target q rest callee typed used calleeFound declared live ready resume ih =>
    have resolved := target_resolved checked found used
    have nested := ih calleeFound
    cases q with
    | call => cases live
    | invoke => simp [Phase.frames, Body.frames]
    | label => exact List.isChain_cons_cons.mpr ⟨resolved, nested⟩
    | returning | exit => exact List.isChain_cons_cons.mpr ⟨resolved, nested⟩
    | done => cases live
  | _ => simp [Phase.frames, Body.frames]

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
