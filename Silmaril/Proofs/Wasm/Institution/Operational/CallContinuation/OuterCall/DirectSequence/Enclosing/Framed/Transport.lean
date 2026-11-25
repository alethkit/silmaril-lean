module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs

open Execution
open Execution.Runtime (Frame)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (ctx : Context)
    (site : Site) (q : State ctx site) :
    (v1Config s caller ctx site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller ctx site q := by
  open Wasm.V1.Execution in
  cases q with
  | label phase =>
    have mapped : codeToLime (Enclosing.v1Code ctx site phase) = Enclosing.limeCode ctx site phase :=
      congrArg Execution.Runtime.Config.code (Enclosing.v1_to_lime s ctx site phase)
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, [.frame ctx.sequence.results.length ctx.frame
      [.label ctx.sequence.results.length [] (codeToLime (Enclosing.v1Code ctx site phase))]]⟩ :
        Wasm.Lime1.Execution.Config H) = _
    rw [mapped]
    rfl
  | exit r =>
    cases r with
    | trap => rfl
    | values stack =>
      change (⟨s.mapCode Wasm.V1.Func.toLime, caller,
        [.frame ctx.sequence.results.length ctx.frame (codeToLime (values stack))]⟩ :
          Wasm.Lime1.Execution.Config H) = _
      rw [map_values]
      rfl
  | done r =>
    cases r with
    | trap => rfl
    | values stack => exact congrArg (fun code => (⟨s.mapCode Wasm.V1.Func.toLime, caller, code⟩ :
        Wasm.Lime1.Execution.Config H)) (map_values stack)

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller : Frame) {ctx : Context}
    {p : Program} (g : Enclosing.LimeGuard s ctx p) (q : State ctx p.site) :
    (limeConfig s caller ctx p.site q).toCore = coreConfig s.toCore caller ctx p.site q := by
  open Wasm.Lime1.Execution in
  cases q with
  | label phase =>
    have mapped : Admin.listToCore s (Enclosing.limeCode ctx p.site phase) = Enclosing.coreCode ctx p.site phase :=
      congrArg Core.Config.code (Enclosing.lime_to_core g phase)
    change (⟨s.toCore, caller.toCore, [.frame ctx.sequence.results.length ctx.frame.toCore
      [.label ctx.sequence.results.length [] (Admin.listToCore s (Enclosing.limeCode ctx p.site phase))]]⟩ :
        Core.Config H) = _
    rw [mapped]
    rfl
  | exit r =>
    cases r with
    | trap => rfl
    | values stack =>
      change (⟨s.toCore, caller.toCore,
        [.frame ctx.sequence.results.length ctx.frame.toCore (Admin.listToCore s (values stack))]⟩ :
          Core.Config H) = _
      rw [CallContinuation.values_toCore]
      rfl
  | done r =>
    cases r with
    | trap => rfl
    | values stack =>
      exact congrArg (fun code => (⟨s.toCore, caller.toCore, code⟩ : Core.Config H))
        (CallContinuation.values_toCore s stack)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs
