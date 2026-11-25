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

private theorem args_check {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {target : CallTarget} {saved operands : List Value} {rest : List Op}
    (count : operands.length = target.declaration.params.length)
    (typed : fn.WellTyped (saved ++ operands) (.call target :: rest) fallthrough enclosing) :
    operands.map Value.type = target.declaration.params ∧ fn.ResumeTyped saved target rest fallthrough enclosing := by
  have length : operands.length = (Prefix.stackTypes operands).length := by simp [Prefix.stackTypes]
  unfold Function.WellTyped at typed
  simp only [checkCode, checkOp, Bool.and_eq_true_iff, decide_eq_true_eq, stack_types_append, ← count, length,
    List.take_left, List.drop_left] at typed
  exact ⟨List.reverse_inj.mp typed.1.2, typed.2⟩

private theorem init_local_types {fn : Function} {args : List Value} (typed : args.map Value.type = fn.declaration.params) :
    (fn.declaration.frame args).locals.map Value.type = fn.localTypes := by
  simp [Declaration.frame, Function.localTypes, List.map_map, Function.comp_def, Value.zero, typed]

private theorem result_of_nil {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {stack : List Value} (typed : fn.WellTyped stack [] fallthrough enclosing) :
    stack.map Value.type = fallthrough := by
  simpa [Function.WellTyped, checkCode, Prefix.stackTypes] using typed

private theorem return_of_code {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {stack : List Value} {rest : List Op}
    (typed : fn.WellTyped stack (.return_ :: rest) fallthrough enclosing) : fn.ReturnTyped stack := by
  simpa [Function.WellTyped, Function.ReturnTyped, SuffixTyped, checkCode, checkOp] using typed

private theorem suffix_result {types : List NumType} {extra results : List Value}
    (typed : SuffixTyped types (extra ++ results)) (arity : results.length = types.length) :
    results.map Value.type = types := by
  have length : (Prefix.stackTypes results).length = types.length := by
    simpa [Prefix.stackTypes] using arity
  unfold SuffixTyped at typed
  rw [stack_types_append, ← length, List.take_left] at typed
  exact List.reverse_inj.mp typed

private theorem numeric_preserves {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {locals stack next : List Value} {op : Prefix.Op} {rest : List Op}
    (typed : locals.map Value.type = fn.localTypes)
    (step : Prefix.Reduce locals stack op (.values next))
    (body : fn.WellTyped stack (.numeric op :: rest) fallthrough enclosing) : fn.WellTyped next rest fallthrough enclosing := by
  have head := Prefix.checkOp_result step
  rw [typed] at head
  simpa [Function.WellTyped, checkCode, checkOp, head] using body

private theorem set_preserves {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {locals next saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
    (typed : locals.map Value.type = fn.localTypes)
    (write : Locals.Edge ⟨locals, [.value v, .set i]⟩ ⟨next, []⟩)
    (body : fn.WellTyped (saved ++ [v]) (.set i :: rest) fallthrough enclosing) :
    next.map Value.type = fn.localTypes ∧ fn.WellTyped saved rest fallthrough enclosing := by
  by_cases fits : fn.localTypes[i.toNat]? = some v.type
  · have localGuard : Locals.Admitted fn.localTypes [] ⟨locals, [.value v, .set i]⟩ :=
      ⟨typed, by simp [Locals.check, fits]⟩
    exact ⟨(Locals.closed localGuard write).1,
      by simpa [Function.WellTyped, checkCode, checkOp, Prefix.stackTypes, Locals.check, fits] using body⟩
  · simp [Function.WellTyped, checkCode, checkOp, Prefix.stackTypes, Locals.check, fits] at body

private theorem tee_preserves {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
    (body : fn.WellTyped (saved ++ [v]) (.tee i :: rest) fallthrough enclosing) :
    fn.WellTyped (saved ++ [v, v]) (.set i :: rest) fallthrough enclosing := by
  by_cases fits : fn.localTypes[i.toNat]? = some v.type <;>
    simp_all [Function.WellTyped, checkCode, checkOp, Prefix.stackTypes, Locals.check]

private theorem suffix_prefix {types : List NumType} {stack saved : List Value}
    (typed : SuffixTyped types stack) : SuffixTyped types (saved ++ stack) := by
  have enough : types.length ≤ (Prefix.stackTypes stack).length := by
    have count := congrArg List.length typed
    simp only [List.length_take, List.length_reverse] at count
    omega
  simpa only [SuffixTyped, stack_types_append, List.take_append_of_le_length enough] using typed

private theorem branching_guard {program : Program} {fn : Function} {fallthrough : List NumType}
    {enclosing : EnclosingLabels} {locals stack : List Value} {depth : LabelIdx} {result : Option NumType}
    (ready : AdmittedAt program fn fallthrough enclosing (.branching locals stack depth result)) :
    locals.map Value.type = fn.localTypes ∧ (enclosing.getD [])[depth.toNat]? = some result.toList ∧
      SuffixTyped result.toList stack := by
  cases ready with | branching typed target payload => exact ⟨typed, target, payload⟩

private theorem returning_guard {program : Program} {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {locals stack : List Value} (ready : AdmittedAt program fn fallthrough enclosing (.returning locals stack)) :
    locals.map Value.type = fn.localTypes ∧ fn.ReturnTyped stack := by
  cases ready with | returning locals stack => exact ⟨locals, stack⟩

private theorem exit_guard {program : Program} {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {locals stack : List Value} (ready : AdmittedAt program fn fallthrough enclosing (.exit locals (.values stack))) :
    locals.map Value.type = fn.localTypes ∧ stack.map Value.type = fallthrough := by
  cases ready with | exit locals stack => exact ⟨locals, stack⟩

private theorem trap_exit_guard {program : Program} {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {locals : List Value} (ready : AdmittedAt program fn fallthrough enclosing (.exit locals .trap)) :
    locals.map Value.type = fn.localTypes := by
  cases ready with | exit locals _ => exact locals

private theorem split_condition {stack : List Value} {resume : List NumType → Bool}
    (typed : checkCondition (Prefix.stackTypes stack) resume = true) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] := by
  cases stack using List.reverseRecOn with
  | nil => simp [Prefix.stackTypes, checkCondition] at typed
  | append_singleton saved v =>
    rcases v with ⟨type, bits⟩
    rw [stack_types_append] at typed
    change checkCondition (type :: Prefix.stackTypes saved) resume = true at typed
    cases type with
    | float kind => simp [checkCondition] at typed
    | int kind =>
      cases kind with
      | i32 => exact ⟨saved, bits, rfl⟩
      | i64 => simp [checkCondition] at typed

theorem split_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {stack : List Value}
    {result : Option NumType} {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped stack (.if_ result thenBody elseBody :: rest) fallthrough enclosing) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] := by
  apply split_condition
  simpa only [Function.WellTyped, checkCode, checkOp] using typed

theorem split_br_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {stack : List Value}
    {result : Option NumType} {depth : LabelIdx} {rest : List Op}
    (typed : fn.WellTyped stack (.brIf depth result :: rest) fallthrough enclosing) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] := by
  apply split_condition
  simpa only [Function.WellTyped, checkCode, checkOp] using typed

theorem checked_branch {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {stack : List Value} {depth : LabelIdx} {result : Option NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing) :
    (branchTargets fallthrough enclosing)[depth.toNat]? = some result.toList ∧ SuffixTyped result.toList stack := by
  simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped] using typed

theorem branch_here_result {fallthrough : List NumType} {enclosing : EnclosingLabels} {result : Option NumType}
    (found : (branchTargets fallthrough enclosing)[(⟨0⟩ : LabelIdx).toNat]? = some result.toList) :
    fallthrough = result.toList := by
  cases enclosing with
  | none => simp [branchTargets] at found
  | some labels =>
    change (fallthrough :: labels)[0]? = some result.toList at found
    exact Option.some.inj found

theorem admitted_step {program : Program} (checked : program.check = true) (address : FuncAddr) :
    ∀ {fn a b fallthrough enclosing}, program.lookup address = some fn → AdmittedAt program fn fallthrough enclosing a →
      program.Edge checked address a b → AdmittedAt program fn fallthrough enclosing b := by
  induction address using (program.table.wellFounded (Program.rankCheck checked)).induction with
  | h address ih =>
    intro fn a b fallthrough enclosing found ready move
    have step := (edge_iff checked found).mp move
    induction step generalizing fallthrough enclosing with
    | resolve args => cases ready with | call typed => exact .invoke typed
    | enter args typed =>
      cases ready
      exact .running (init_local_types typed) (check_function checked found)
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
    | ifSelect locals saved condition result thenBody elseBody rest =>
      cases ready with
      | running typed body =>
        unfold Function.WellTyped at body
        rw [stack_types_append] at body
        change checkCode _ _ _ _ _ (.int .i32 :: Prefix.stackTypes saved) _ = true at body
        simp only [checkCode, checkOp, checkCondition, Bool.and_eq_true_iff] at body
        apply AdmittedAt.running typed
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff]
        split
        · exact ⟨body.1.2, body.2⟩
        · exact ⟨body.1.1, body.2⟩
    | blockEnter locals saved result code rest =>
      cases ready with
      | running typed body =>
        have both := body
        simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff] at both
        exact .block (.running typed both.1) both.2
    | @blockStep locals saved result rest inner next step bodyIH =>
      cases ready with
      | block inside resume =>
        have outcome := label_outcome step ⟨_, _, rfl⟩
        have after := bodyIH inside ((edge_iff checked found).mpr step)
        cases next with
        | label => exact .block after resume
        | branching =>
          obtain ⟨typed, target, payload⟩ := branching_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, checkBranch, decide_eq_true_eq, SuffixTyped, Option.getD_some] using
              And.intro target (suffix_prefix (saved := saved) payload))
        | returning =>
          obtain ⟨typed, out⟩ := returning_guard after
          exact .running typed (by
            simpa only [Function.WellTyped, checkCode, checkOp, Function.ReturnTyped, SuffixTyped, decide_eq_true_eq] using
              suffix_prefix (saved := saved) out)
        | exit locals out =>
          cases out with
          | values stack =>
            obtain ⟨typed, outTyped⟩ := exit_guard after
            exact .running typed (by simpa [Function.WellTyped, stack_types_append,
              Prefix.stackTypes, outTyped] using resume)
          | trap => exact .trapped (trap_exit_guard after)
        | call | invoke | done => cases outcome
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
        | block inside body => exact .active typed used childFound declared trivial (.block inside body) resume
        | trapped newArgs => exact .active typed used childFound declared trivial (.trapped newArgs) resume
        | branching _ target _ => simp at target
        | returning newArgs out => exact .active typed used childFound declared trivial (.returning newArgs out) resume
        | exit newArgs out => exact .active typed used childFound declared trivial (.exit newArgs out) resume
        | @done _ _ _ result out =>
          cases result with
          | trap => exact .trapped typed
          | values stack =>
            have values : stack.map Value.type = target.declaration.results :=
              out.trans (congrArg Declaration.results declared)
            exact .running typed (by simpa [Function.WellTyped, Function.ResumeTyped, stack_types_append,
              Prefix.stackTypes, values] using resume)
    | discard cut => cases ready with | trapped typed => exact .trapped typed
    | branchIf locals stack condition depth result rest =>
      cases ready with
      | running typed body =>
        unfold Function.WellTyped at body
        rw [stack_types_append] at body
        change checkCode _ _ _ _ _ (.int .i32 :: Prefix.stackTypes stack) _ = true at body
        simp only [checkCode, checkOp, checkCondition, Bool.and_eq_true_iff] at body
        apply AdmittedAt.running typed
        split
        · exact body.2
        · exact body.1
    | branchHere locals extra values result rest arity =>
      cases ready with
      | running typed body =>
        obtain ⟨target, payload⟩ := checked_branch body
        exact .exit typed ((suffix_result payload arity).trans (branch_here_result target).symm)
    | branchOuter locals stack depth result rest outer =>
      cases ready with
      | running typed body =>
        obtain ⟨target, payload⟩ := checked_branch body
        cases enclosing with
        | none => simp [branchTargets] at target
        | some labels =>
          obtain ⟨index, eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt outer)
          refine .branching typed ?_ payload
          change labels[depth.toNat - 1]? = some result.toList
          simpa [eq] using (show (fallthrough :: labels)[depth.toNat]? = _ from target)
    | returnLabel _ _ _ =>
      cases ready with | running typed body => exact .returning typed (return_of_code body)
    | returnFrame _ _ _ arity =>
      cases ready with | returning _ out => exact .done (suffix_result out arity)
    | leaveValues args stack =>
      cases ready with | running typed body => exact .exit typed (result_of_nil body)
    | leaveTrap args => cases ready with | trapped typed => exact .exit typed trivial
    | leaveFrame args result typed => exact .done typed

theorem nesting_of_admitted {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {phase : Phase} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    (found : program.lookup address = some fn)
    (ready : AdmittedAt program fn fallthrough enclosing phase) : program.table.Nesting (phase.frames address) := by
  induction ready generalizing address with
  | @active fn _ _ args saved target q rest callee typed used calleeFound declared live ready resume ih =>
    have resolved := target_resolved checked found used
    have nested := ih calleeFound
    cases q with
    | call | branching => cases live
    | invoke => simp [Phase.frames, Body.frames]
    | label => exact List.isChain_cons_cons.mpr ⟨resolved, nested⟩
    | returning | exit => exact List.isChain_cons_cons.mpr ⟨resolved, nested⟩
    | done => cases live
  | block _ _ ih => exact ih found
  | _ => simp [Phase.frames, Body.frames]

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
