module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Core
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.SingleThreaded.Determinism.Stuck

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs

open Execution
open Execution.Runtime (FuncAddr Value)
open Wasm.Numerics (Profile)
open Wasm.Validation (Expand Ty)
open Wasm.SingleThreaded.Det (noHost)

theorem core_resolve_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame}
    {i : FuncIdx} {address : FuncAddr} {fn : Outer} {args : List Value} {dst : Core.Config H}
    (found : caller.module.funcs[i.toNat]? = some address)
    (allocated : s.funcs[address.value]? = some fn.coreInstance) :
    Core.Step P noHost (coreUnresolved s caller i args) dst ↔ dst = coreResolved s caller address fn args := by
  have index : caller.toCore.module.funcs[i.toNat]? = some address.value := by
    change (caller.module.funcs.map (fun a : FuncAddr => a.value))[i.toNat]? = _
    simp [found]
  constructor
  · intro h
    obtain ⟨a, fi, ha, hf, eq⟩ := Core.Step.call_vals_inv h
    rw [index] at ha
    cases ha
    rw [allocated] at hf
    cases hf
    exact eq
  · rintro rfl
    exact Core.Sim.Step.vals_left (Core.Step.call index allocated) _

private theorem frame_init (fn : Outer) (args : List Value) :
    Core.Frame.forCall fn.moduleInst.toCore (args.map Value.toCore) fn.coreFunc.locals = (fn.frame args).toCore := by
  simp only [Core.Frame.forCall, Outer.coreFunc, Outer.frame, Runtime.Frame.toCore, List.map_append,
    List.map_map]
  congr 2
  change (fn.locals.map Wasm.V1.ValType.toCore).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  cases t <;> rfl

private theorem core_expression (fn : Outer) :
    Core.expression fn.coreBody = coreValues fn.innerArgs ++ [.plain (.call fn.innerIndex), .plain .nop] := by
  have one (v : Value) : (Locals.coreCodec.emit (.value v)) = v.toCore.toAdmin := by
    rcases v with ⟨ty, bits⟩
    cases ty <;> rfl
  simp only [Outer.coreBody, Core.expression, List.map_append, List.map_cons, List.map_nil]
  rw [List.map_map]
  change Locals.coreCodec.encode (Locals.values fn.innerArgs) ++ _ = _
  simp [Locals.Codec.encode, Locals.values, Core.vals, List.map_map, one]

theorem core_entry_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame}
    {address : FuncAddr} {fn : Outer} {args : List Value} {dst : Core.Config H}
    (typed : args.map Value.type = fn.params)
    (allocated : s.funcs[address.value]? = some fn.coreInstance) :
    Core.Step P noHost (coreResolved s caller address fn args) dst ↔ dst = coreEntered s caller fn args := by
  have sig : Expand fn.type.toDefType (.func (Ty.ofList (fn.params.map Ty.num))
      (Ty.ofList (fn.inner.result.toList.map Ty.num))) :=
    Expand.iff.mpr (Wasm.V1.FuncType.toDefType_expand _)
  have count : (args.map Value.toCore).length = (Ty.ofList (fn.params.map Ty.num)).length := by
    have len := congrArg List.length typed
    simpa [Ty.length_ofList] using len
  constructor
  · intro step
    have read := Core.Step.callRef_wasm_inv_exact (r := .callRefType fn.type.toDefType)
      (code := fn.coreFunc) (by trivial) allocated rfl sig count step
    simpa [coreEntered, Outer.coreInstance, Outer.arity, CallFrame.Callee.arity, Ty.length_ofList,
      frame_init, show Core.expression fn.coreFunc.body = _ from core_expression fn] using read
  · rintro rfl
    have h := Core.Step.callRefFunc (P := P) (host := noHost) (f := caller.toCore)
      (vs := args.map Value.toCore) (c := .callRefType fn.type.toDefType) trivial allocated sig count rfl
    simpa [coreResolved, coreEntered, Outer.coreInstance, Outer.arity, CallFrame.Callee.arity, Ty.length_ofList,
      frame_init, show Core.expression fn.coreFunc.body = _ from core_expression fn] using h

theorem core_inner_resolve_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame}
    {address : FuncAddr} {fn : Outer} {args : List Value} {dst : Core.Config H}
    (found : fn.moduleInst.funcs[fn.innerIndex.toNat]? = some address)
    (allocated : s.funcs[address.value]? = some fn.inner.coreInstance) :
    Core.Step P noHost (coreEntered s caller fn args) dst ↔
      dst = Nested.coreConfig s caller (fn.frame args) address fn.inner fn.arity
        (.label (.active (.invoke [] fn.innerArgs))) := by
  have index : (fn.frame args).toCore.module.funcs[fn.innerIndex.toNat]? = some address.value := by
    change (fn.moduleInst.funcs.map (fun a : FuncAddr => a.value))[fn.innerIndex.toNat]? = _
    simp [found]
  constructor
  · intro step
    rcases Core.Step.frame_inv step with ⟨_, _, _, body, rfl⟩ | ⟨_, bad, _⟩
    · rcases Core.Step.label_inv body with ⟨_, _, _, call, eq⟩ | ⟨_, bad, _⟩
      · obtain ⟨a, f, ha, hf, result⟩ := Core.Step.call_vals_inv_seq
          (vs := fn.innerArgs.map Value.toCore) (x := fn.innerIndex) (rest := [.plain .nop]) call
        rw [index] at ha
        cases ha
        rw [allocated] at hf
        cases hf
        cases result
        cases eq
        simp only [Nested.coreConfig, Nested.coreCode, Nested.render, CallContinuation.coreCode,
          CallContinuation.render, CallFrame.coreCode, List.nil_append, List.append_assoc]
        rfl
      · generalize h : coreValues fn.innerArgs ++ [.plain (.call fn.innerIndex), .plain .nop] = code at bad
        have active := congrArg (fun c => (Wasm.SingleThreaded.Det.fnv c).2) h
        cases bad with
        | returnCall e =>
          have none := Core.Admin.val?_of_isReturnCallRef e
          simp [Wasm.SingleThreaded.Det.fnv_cons_of_none none,
            Wasm.SingleThreaded.Det.fnv_cons_of_none (a := .plain (.call fn.innerIndex)) rfl] at active
          rw [← active.1] at e
          contradiction
        | _ =>
          simp [Core.throwing, Wasm.SingleThreaded.Det.fnv_cons_of_none (a := .plain (.call fn.innerIndex)) rfl,
            Wasm.SingleThreaded.Det.fnv_cons_of_none (a := .plain .return_) rfl,
            Wasm.SingleThreaded.Det.fnv_cons_of_none (a := .plain .throwRef) rfl,
            Wasm.SingleThreaded.Det.fnv_cons_of_none (a := .plain (.br _)) rfl] at active
    · exact (CallContinuation.Proofs.frame_label_stays bad).elim
  · intro eq
    subst dst
    have step := Core.Step.call (P := P) (host := noHost) (f := (fn.frame args).toCore) index allocated
    have extended := Core.Sim.Step.append_right step [.plain .nop]
    have lifted := Core.Sim.Step.vals_left extended (fn.innerArgs.map Value.toCore)
    have whole := Core.Step.ctxtFrame (f := caller.toCore) (n := fn.arity)
      (Core.Step.ctxtLabel (n := fn.arity) (cont := []) lifted)
    simpa [coreEntered, Nested.coreConfig, Nested.coreCode, Nested.render, CallContinuation.coreCode,
      CallContinuation.render, CallFrame.coreCode, CallFrame.Callee.coreInstance, List.append_assoc] using whole

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : CallSite}
    {a b : State} (guard : CoreGuard s caller site) (edge : Edge site a b) :
    Core.Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) := by
  cases invert edge with
  | ground h =>
    cases h with
    | resolve => exact (core_resolve_iff guard.outerLookup guard.outerAlloc).mpr rfl
    | enter => exact (core_entry_iff guard.typed.outerArgs guard.outerAlloc).mpr rfl
    | resolveInner => exact (core_inner_resolve_iff guard.innerLookup guard.innerAlloc).mpr rfl
  | nest h => exact Nested.core_sound guard.innerAlloc h

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : CallSite}
    {a : State} {b : Core.Config H} (guard : CoreGuard s caller site) (ready : Admitted site a) :
    Core.Step P noHost (coreConfig s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = coreConfig s caller site out := by
  constructor
  · intro step
    cases a with
    | call => exact ⟨.invoke, fact .resolve, (core_resolve_iff guard.outerLookup guard.outerAlloc).mp step⟩
    | invoke => exact ⟨.entered, fact .enter, (core_entry_iff guard.typed.outerArgs guard.outerAlloc).mp step⟩
    | entered =>
      exact ⟨.nested site.start, fact .resolveInner, (core_inner_resolve_iff guard.innerLookup guard.innerAlloc).mp step⟩
    | nested a =>
      obtain ⟨out, move, eq⟩ := (Nested.core_step_iff guard.innerAlloc ready).mp step
      exact ⟨.nested out, delegate move, eq⟩
  · rintro ⟨out, move, rfl⟩
    exact core_sound guard move

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs
