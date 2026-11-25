module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs

open Execution
open Execution.Runtime (Frame)

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    (g : V1Guard s caller site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller site where
  toNativeLookups := g.toNativeLookups
  outerAlloc := by
    rw [Runtime.Store.mapCode_funcs_getElem?, g.outerAlloc]
    rfl
  innerAlloc := CallFrame.allocated_toLime g.innerAlloc

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) : CoreGuard s.toCore caller site where
  toNativeLookups := g.toNativeLookups
  outerAlloc := by
    change (s.funcs.map Runtime.FuncInst.toCore)[site.outerAddr.value]? = _
    rw [List.getElem?_map, g.outerAlloc]
    rfl
  innerAlloc := CallFrame.allocated_toCore g.innerAlloc

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State site) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q := by
  cases q with
  | call | invoke =>
    simp only [v1Config, v1Code, limeConfig, limeCode, render, Wasm.V1.Execution.Config.toLime,
      Wasm.V1.Execution.codeToLime_append, Wasm.V1.Execution.map_values]
    rfl
  | nested q => exact Nested.v1_to_lime s caller _ _ _ _ q
  | _ => rfl

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) (q : State site) :
    (limeConfig s caller site q).toCore = coreConfig s.toCore caller site q := by
  cases q with
  | call =>
    change (⟨_, _, Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.values site.args ++ [.source (.call site.outerIndex)])⟩ : Core.Config H) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    rfl
  | invoke =>
    change (⟨_, _, Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.values site.args ++ [.invoke site.outerAddr])⟩ : Core.Config H) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    have ty : s.funcDefType site.outerAddr = site.type.toDefType := by
      simp [Runtime.Store.funcDefType, Runtime.FuncInst.type, g.outerAlloc]
    change (⟨s.toCore, caller.toCore, coreValues site.args ++ [.ref (.func site.outerAddr.value),
      .callRefType (s.funcDefType site.outerAddr)]⟩ : Core.Config H) = _
    rw [ty]
    rfl
  | nested q => exact Nested.lime_to_core caller _ g.innerAlloc _ q
  | _ => rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs
