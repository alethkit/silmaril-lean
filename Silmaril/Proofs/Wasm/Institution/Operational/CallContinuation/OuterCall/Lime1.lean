module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1Head
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs.Lime1

open Execution
open Execution.Runtime (Frame FuncAddr Value AdminInstr)
open Wasm.Lime1.Execution
open CallContinuation.Proofs.Lime1 (first first_value first_prefix first_head first_values peel wrapper_step frame_label_stays)

private theorem call_seq {H : Type} {src dst : Config H} (step : Step CallFrame.limeNoHost src dst)
    {vs : List Value} {i : FuncIdx} {rest : List Admin} (source : src.code = values vs ++ .source (.call i) :: rest) :
    ∃ addr, src.frame.module.funcs[i.toNat]? = some addr ∧
      dst = ⟨src.store, src.frame, values vs ++ .invoke addr :: rest⟩ := by
  induction step generalizing vs rest with
  | @context s s' f f' before after step saved tail ih =>
    obtain ⟨args, cut, rfl, inside, rfl⟩ := peel step.nonvalue source rfl
    obtain ⟨addr, lookup, eq⟩ := ih inside
    refine ⟨addr, lookup, ?_⟩
    change (⟨s', f', values saved ++ after ++ tail⟩ : Config H) = _
    change (⟨s', f', after⟩ : Config H) = _ at eq
    have lifted := congrArg (fun c : Config H =>
      (⟨c.store, c.frame, values saved ++ c.code ++ tail⟩ : Config H)) eq
    simpa only [values_append, List.append_assoc, List.cons_append] using lifted
  | call s f j addr found =>
    have len := congrArg List.length source
    simp at len
    have hv : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst vs rest
    have eq : j = i := Wasm.Lime1.Instr.call.inj (AdminInstr.source.inj (List.cons.inj source).1)
    subst j
    exact ⟨addr, found, rfl⟩
  | pure _ _ h =>
    have active : first (values vs ++ .source (.call i) :: rest) = some (.source (.call i)) := by
      rw [first_prefix]
      exact first_head rest rfl
    have seen := (congrArg first source).trans active
    cases h <;>
      simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at seen <;>
      simp [first, asValue?] at seen
  | invokeHost | invokeHostDiverges => contradiction
  | _ =>
    have active : first (values vs ++ .source (.call i) :: rest) = some (.source (.call i)) := by
      rw [first_prefix]
      exact first_head rest rfl
    have seen := (congrArg first source).trans active
    simp only [first_value, first_prefix] at seen
    simp [first, asValue?] at seen

private theorem label_call_stays {types : List Wasm.Lime1.FuncType} {n : Nat}
    {vs : List Value} {i : FuncIdx} {out : List Admin}
    (h : PureStep types [.label n [] (values vs ++ [.source (.call i), .source .nop])] out) : False := by
  generalize eq : ([.label n [] (values vs ++ [.source (.call i), .source .nop])] : List Admin) = before at h
  cases h with
  | labelDone | labelBranch | labelBranchOuter | labelReturn | labelTrap =>
    have code := (AdminInstr.label.inj (List.cons.inj eq).1).2.2
    have seen := congrArg first code
    simp only [List.append_assoc, List.singleton_append, first_prefix, first_values] at seen
    simp [first, asValue?] at seen
  | trapValues | trapTail =>
    have len := congrArg List.length eq
    simp [values] at len
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values, List.getLast?_append] at last

private theorem lime_expression (fn : Outer) :
    expression (limeBody fn) = values fn.innerArgs ++ [.source (.call fn.innerIndex), .source .nop] := by
  have one (v : Value) : Locals.limeCodec.emit (.value v) = value v := by
    rcases v with ⟨ty, bits⟩
    cases ty <;> rfl
  simp only [limeBody, expression, List.map_append, List.map_cons, List.map_nil, List.map_map]
  change Locals.limeCodec.encode (Locals.values fn.innerArgs) ++ _ = _
  simp [Locals.Codec.encode, Locals.values, values, List.map_map, one]

theorem lime_resolve_iff {H : Type} {s : Store H} {caller : Frame}
    {i : FuncIdx} {address : FuncAddr} {args : List Value} {dst : Config H}
    (found : caller.module.funcs[i.toNat]? = some address) :
    Step CallFrame.limeNoHost (limeUnresolved s caller i args) dst ↔ dst = limeResolved s caller address args := by
  constructor
  · intro h
    obtain ⟨a, lookup, result⟩ := call_seq h rfl
    change caller.module.funcs[i.toNat]? = some a at lookup
    rw [found] at lookup
    cases lookup
    exact result
  · rintro rfl
    simpa only [limeUnresolved, limeResolved, List.append_nil] using
      Step.context (Step.call (host := CallFrame.limeNoHost) s caller i address found) args []

theorem lime_entry_iff {H : Type} {s : Store H} {caller : Frame}
    {address : FuncAddr} {fn : Outer} {args : List Value} {dst : Config H}
    (typed : args.map Value.type = fn.params)
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.moduleInst (limeFunc fn))) :
    Step CallFrame.limeNoHost (limeResolved s caller address args) dst ↔ dst = limeEntered s caller fn args := by
  have len : args.length = fn.type.params.length := by
    simpa [Outer.type] using congrArg List.length typed
  have h := CallFrame.lime_invoke_wasm_exact (caller := caller) allocated len (dst := dst)
  simpa [limeResolved, limeEntered, Outer.type, Outer.arity, CallFrame.Callee.arity, Outer.frame, limeFunc,
    lime_expression] using h

theorem lime_inner_resolve_iff {H : Type} {s : Store H} {caller : Frame}
    {address : FuncAddr} {fn : Outer} {args : List Value} {dst : Config H}
    (found : fn.moduleInst.funcs[fn.innerIndex.toNat]? = some address) :
    Step CallFrame.limeNoHost (limeEntered s caller fn args) dst ↔
      dst = Nested.limeConfig s caller (fn.frame args) address fn.inner fn.arity
        (.label (.active (.invoke [] fn.innerArgs))) := by
  constructor
  · intro step
    cases wrapper_step step rfl trivial with
    | pure impossible => exact (frame_label_stays impossible).elim
    | frame outerStep =>
      cases wrapper_step outerStep rfl trivial with
      | pure impossible => exact (label_call_stays impossible).elim
      | label innerStep =>
        obtain ⟨a, lookup, read⟩ := call_seq innerStep
          (vs := fn.innerArgs) (i := fn.innerIndex) (rest := [.source .nop]) rfl
        change fn.moduleInst.funcs[fn.innerIndex.toNat]? = some a at lookup
        rw [found] at lookup
        cases lookup
        rw [read]
        simp [limeEntered, Nested.limeConfig, Nested.limeCode, Nested.render, CallContinuation.limeCode,
          CallContinuation.render, CallFrame.limeCode, CallFrame.legacyCode, values, List.append_assoc]
  · rintro rfl
    have step := Step.call (host := CallFrame.limeNoHost) s (fn.frame args) fn.innerIndex address found
    have whole := Step.frame (Step.label (Step.context step fn.innerArgs [.source .nop]) fn.arity []) fn.arity caller
    simpa only [limeEntered, Nested.limeConfig, Nested.limeCode, Nested.render, CallContinuation.limeCode,
      CallContinuation.render, CallFrame.limeCode, CallFrame.legacyCode, values, List.nil_append, List.append_assoc, List.singleton_append] using whole

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : CallSite}
    {a b : State} (g : LimeGuard s caller site) (edge : Edge site a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) := by
  cases invert edge with
  | ground h =>
    cases h with
    | resolve => exact (lime_resolve_iff g.outerLookup).mpr rfl
    | enter => exact (lime_entry_iff g.typed.outerArgs g.outerAlloc).mpr rfl
    | resolveInner => exact (lime_inner_resolve_iff g.innerLookup).mpr rfl
  | nest h => exact Nested.lime_sound g.innerAlloc h

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : CallSite}
    {a : State} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = limeConfig s caller site out := by
  constructor
  · intro step
    cases a with
    | call => exact ⟨.invoke, fact .resolve, (lime_resolve_iff g.outerLookup).mp step⟩
    | invoke => exact ⟨.entered, fact .enter, (lime_entry_iff g.typed.outerArgs g.outerAlloc).mp step⟩
    | entered => exact ⟨.nested site.start, fact .resolveInner, (lime_inner_resolve_iff g.innerLookup).mp step⟩
    | nested a =>
      obtain ⟨out, move, eq⟩ := (Nested.lime_step_iff g.innerAlloc ready).mp step
      exact ⟨.nested out, delegate move, eq⟩
  · rintro ⟨out, move, rfl⟩
    exact lime_sound g move

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs.Lime1
