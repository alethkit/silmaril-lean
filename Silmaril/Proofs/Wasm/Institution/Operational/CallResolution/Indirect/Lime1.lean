module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall.Ranked.Graph (Program Function)

open CallContinuation.OuterCall.Computed in
theorem lookup_stays {H : Type} {s : Store H} {site : Site} {caller : Frame} {selector : BitVec 32}
    {stack : List Value} {rest : List Admin} (n : Nat) (out : List Admin) :
    ¬ PureStep caller.module.types [.label n [] (limeSource s caller site selector stack rest).code] out :=
  lime_label_stays (head := .source (.callIndirect site.typeIndex)) rfl
    (by simp) (by simp) (by simp)

open CallContinuation.OuterCall.Computed in
theorem invoke_stays {H : Type} {s : Store H} {addr : Execution.Runtime.FuncAddr} {caller : Frame}
    {stack : List Value} {rest : List Admin} (n : Nat) (out : List Admin) :
    ¬ PureStep caller.module.types [.label n [] (limeResolved s caller stack rest (.resolved addr)).code] out :=
  lime_label_stays (head := .invoke addr) rfl (by simp) (by simp) (by simp)

theorem step_iff {H : Type} {s : Store H} {caller : Frame} {site : Site} {program : Program}
    {selector : BitVec 32} {stack : List Value} {rest : List Admin} {out : Outcome} {dst : Config H}
    (checked : site.check program caller = true) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s caller = some site.table) (resolved : site.resolve program selector = some out) :
    Step CallFrame.limeNoHost (limeSource s caller site selector stack rest) dst ↔
      dst = limeResolved s caller stack rest out := by
  have typeFound := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
  rw [limeSource, CallContinuation.OuterCall.Computed.lime_call_indirect_iff tableFound typeFound]
  cases resolve_iff.mp resolved with
  | bounds entry => simp [entry, limeResolved]
  | null entry => simp [entry, limeResolved]
  | mismatch entry found different =>
    have slot := allocated _ _ found
    simp [entry, slot, limeResolved, Execution.Runtime.FuncInst.type, different]
  | resolved entry found same =>
    have slot := allocated _ _ found
    simp [entry, slot, limeResolved, Execution.Runtime.FuncInst.type, same]

theorem enter_iff {H : Type} {s : Store H} {caller : Frame} {site : Site} {program : Program}
    {selector : BitVec 32} {addr : Execution.Runtime.FuncAddr} {fn : Function}
    {saved args : List Value} {rest : List Admin} {dst : Config H}
    (allocated : program.LimeAllocated s) (found : program.lookup addr = some fn)
    (resolved : site.resolve program selector = some (.resolved addr))
    (typed : args.map Value.type = site.signature.params) :
    Step CallFrame.limeNoHost (limeResolved s caller (saved ++ args) rest (.resolved addr)) dst ↔
      dst = limeEntered s caller fn saved args rest := by
  have same := resolved_signature resolved found
  have params : args.map Value.type = fn.declaration.type.params := by rwa [same]
  have count : args.length = fn.declaration.type.params.length := by
    simpa using congrArg List.length params
  have enter (next : Config H) := CallFrame.lime_invoke_wasm_prefix_iff (caller := caller) (saved := saved)
    (dst := next) (allocated _ _ found) count
  have locals : fn.limeFunc.locals = fn.declaration.locals := rfl
  constructor
  · intro move
    obtain ⟨mid, step, eq⟩ := CallContinuation.lime_invoke_strip_suffix move
    obtain rfl := (enter mid).mp step
    simpa only [limeEntered, locals, CallContinuation.OuterCall.Declaration.frame, List.append_assoc, List.singleton_append] using eq
  · rintro rfl
    have step := (enter _).mpr rfl
    simpa only [limeResolved, limeEntered, locals, CallContinuation.OuterCall.Declaration.frame, values, List.map_nil, List.nil_append, List.append_assoc,
      List.singleton_append] using Step.context step [] rest

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.Lime1
