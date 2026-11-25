module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs

open Execution
open Execution.Runtime (Frame FuncAddr)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller outer : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) (q : State) :
    (v1Config s caller outer addr fn arity q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller outer addr fn arity q := by
  have mapped (a : CallContinuation.State) :
      Wasm.V1.Execution.codeToLime (CallContinuation.v1Code addr fn a) =
        CallContinuation.limeCode addr fn a :=
    congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) (CallContinuation.v1_to_lime s outer addr fn a)
  cases q with
  | label a =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller,
      [.frame arity outer [.label arity [] (Wasm.V1.Execution.codeToLime (CallContinuation.v1Code addr fn a))]]⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [mapped]
    rfl
  | exit r =>
    cases r with
    | trap => rfl
    | values stack =>
      change (⟨s.mapCode Wasm.V1.Func.toLime, caller,
        [.frame arity outer (Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values stack))]⟩ :
        Wasm.Lime1.Execution.Config H) = _
      rw [Wasm.V1.Execution.map_values]
      rfl
  | done r =>
    cases r with
    | trap => rfl
    | values stack =>
      exact congrArg (fun code => (⟨s.mapCode Wasm.V1.Func.toLime, caller, code⟩ :
        Wasm.Lime1.Execution.Config H)) (Wasm.V1.Execution.map_values stack)

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller outer : Frame)
    {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc)) (arity : Nat) (q : State) :
    (limeConfig s caller outer addr fn arity q).toCore =
      coreConfig s.toCore caller outer addr fn arity q := by
  have mapped (a : CallContinuation.State) : Wasm.Lime1.Execution.Admin.listToCore s
      (CallContinuation.limeCode addr fn a) = CallContinuation.coreCode addr fn a :=
    congrArg Core.Config.code (CallContinuation.lime_to_core outer allocated a)
  cases q with
  | label a =>
    change (⟨s.toCore, caller.toCore, [.frame arity outer.toCore [.label arity []
      (Wasm.Lime1.Execution.Admin.listToCore s (CallContinuation.limeCode addr fn a))]]⟩ : Core.Config H) = _
    rw [mapped]
    rfl
  | exit r =>
    cases r with
    | trap => rfl
    | values stack =>
      change (⟨s.toCore, caller.toCore, [.frame arity outer.toCore
        (Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values stack))]⟩ : Core.Config H) = _
      rw [CallContinuation.Proofs.core_values]
      rfl
  | done r =>
    cases r with
    | trap => rfl
    | values stack =>
      exact congrArg (fun code => (⟨s.toCore, caller.toCore, code⟩ : Core.Config H))
        (CallContinuation.Proofs.core_values s stack)

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Proofs
