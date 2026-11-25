module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs

open Execution
open Execution.Runtime (Frame Value)

private theorem func_to_lime (fn : Outer) : (v1Func fn).toLime = limeFunc fn := by
  have literal (v : Value) : (Locals.v1Instr (.value v)).toLime = Locals.limeInstr (.value v) := by
    rcases v with ⟨ty, bits⟩
    cases ty <;> rfl
  simp [v1Func, limeFunc, limeBody, Wasm.V1.Func.toLime, Wasm.V1.Expr.toLime_eq_map,
    List.map_append, List.map_map, Locals.values, Function.comp_def, literal]
  exact ⟨rfl, rfl⟩

private theorem func_to_core (fn : Outer) : (limeFunc fn).toCore = fn.coreFunc := by
  have literal (v : Value) : (Locals.limeInstr (.value v)).toCore = Locals.coreInstr (.value v) := by
    rcases v with ⟨ty, bits⟩
    cases ty <;> rfl
  simp [limeFunc, limeBody, Outer.coreFunc, Outer.coreBody, Wasm.Lime1.Func.toCore,
    Wasm.Lime1.Expr.toCore_eq_map, List.map_append, List.map_map, Locals.values, Function.comp_def, literal]
  exact ⟨rfl, rfl⟩

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : CallSite}
    (g : V1Guard s caller site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller site where
  typed := g.typed
  outerLookup := g.outerLookup
  innerLookup := g.innerLookup
  outerAlloc := by
    rw [Runtime.Store.mapCode_funcs_getElem?, g.outerAlloc]
    simp [Runtime.FuncInst.mapCode, func_to_lime]
  innerAlloc := CallFrame.allocated_toLime g.innerAlloc

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : CallSite}
    (g : LimeGuard s caller site) : CoreGuard s.toCore caller site where
  typed := g.typed
  outerLookup := g.outerLookup
  innerLookup := g.innerLookup
  outerAlloc := by
    change (s.funcs.map Runtime.FuncInst.toCore)[site.outerAddr.value]? = _
    rw [List.getElem?_map, g.outerAlloc]
    simp [Runtime.FuncInst.toCore, Outer.coreInstance, func_to_core]
  innerAlloc := CallFrame.allocated_toCore g.innerAlloc

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : CallSite) (q : State) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q := by
  have mapped (xs : List Value) (tail : List Wasm.V1.Execution.Admin) :
      Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values xs ++ tail) =
        Wasm.Lime1.Execution.values xs ++ Wasm.V1.Execution.codeToLime tail := by
    rw [Wasm.V1.Execution.codeToLime_append, Wasm.V1.Execution.map_values]
  cases q with
  | call =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, Wasm.V1.Execution.codeToLime
      (Wasm.V1.Execution.values site.args ++ [.source (.call site.outerIndex)])⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [mapped]
    rfl
  | invoke =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, Wasm.V1.Execution.codeToLime
      (Wasm.V1.Execution.values site.args ++ [.invoke site.outerAddr])⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [mapped]
    rfl
  | entered =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, [.frame site.callee.arity (site.callee.frame site.args)
      [.label site.callee.arity [] (Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values site.callee.innerArgs ++
        [.source (.call site.callee.innerIndex), .source .nop]))]]⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [mapped]
    rfl
  | nested phase => exact Nested.v1_to_lime s caller _ _ _ _ phase

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : CallSite}
    (g : LimeGuard s caller site) (q : State) :
    (limeConfig s caller site q).toCore = coreConfig s.toCore caller site q := by
  have mapped (xs : List Value) (tail : List Wasm.Lime1.Execution.Admin) :
      Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values xs ++ tail) =
        coreValues xs ++ Wasm.Lime1.Execution.Admin.listToCore s tail := by
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
  cases q with
  | call =>
    change (⟨s.toCore, caller.toCore, Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.values site.args ++ [.source (.call site.outerIndex)])⟩ : Core.Config H) = _
    rw [mapped]
    rfl
  | invoke =>
    change (⟨s.toCore, caller.toCore, Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.values site.args ++ [.invoke site.outerAddr])⟩ : Core.Config H) = _
    rw [mapped]
    have ty : s.funcDefType site.outerAddr = site.callee.type.toDefType := by
      simp [Runtime.Store.funcDefType, Runtime.FuncInst.type, g.outerAlloc]
    change (⟨s.toCore, caller.toCore, coreValues site.args ++ [.ref (.func site.outerAddr.value),
      .callRefType (s.funcDefType site.outerAddr)]⟩ : Core.Config H) = _
    rw [ty]
    rfl
  | entered =>
    change (⟨s.toCore, caller.toCore, [.frame site.callee.arity (site.callee.frame site.args).toCore
      [.label site.callee.arity [] (Wasm.Lime1.Execution.Admin.listToCore s
        (Wasm.Lime1.Execution.values site.callee.innerArgs ++
          [.source (.call site.callee.innerIndex), .source .nop]))]]⟩ : Core.Config H) = _
    rw [mapped]
    rfl
  | nested phase => exact Nested.lime_to_core caller _ g.innerAlloc _ phase

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Proofs
