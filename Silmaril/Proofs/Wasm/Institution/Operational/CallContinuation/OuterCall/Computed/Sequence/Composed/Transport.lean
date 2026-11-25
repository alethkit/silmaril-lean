module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport
import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs

open Execution
open Execution.Runtime (Frame)

private theorem func_to_lime (site : Site) : site.v1Func.toLime = site.limeFunc := by
  have body : Wasm.V1.Expr.toLime site.v1Func.body = site.limeFunc.body := by
    change Wasm.V1.Expr.toLime (site.body v1Source) = site.body limeSource
    simp only [Site.body, Wasm.V1.Expr.toLime_eq_map, List.map_map]
    apply List.map_congr_left
    intro ins _
    cases ins with
    | op op => cases op <;> rfl
    | call => rfl
  exact congrArg (fun body => (⟨site.typeIndex, site.locals, body⟩ : Wasm.Lime1.Func)) body

private theorem func_to_core (site : Site) : site.limeFunc.toCore = site.coreFunc := by
  have body : Wasm.Lime1.Expr.toCore site.limeFunc.body = site.coreFunc.body := by
    change Wasm.Lime1.Expr.toCore (site.body limeSource) = site.body coreSource
    simp only [Site.body, Wasm.Lime1.Expr.toCore_eq_map, List.map_map]
    apply List.map_congr_left
    intro ins _
    cases ins with
    | op op => cases op <;> rfl
    | call => rfl
  exact congrArg (fun body => (⟨site.typeIndex, site.locals.map Wasm.V1.ValType.toCore, body⟩ : Wasm.Func)) body

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    (g : V1Guard s caller site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller site where
  toLookups := g.toLookups
  outerAlloc := by
    rw [Runtime.Store.mapCode_funcs_getElem?, g.outerAlloc]
    simp [Runtime.FuncInst.mapCode, func_to_lime]
  innerGuard := StraightLine.guard_to_lime g.innerGuard

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) : CoreGuard s.toCore caller site where
  toLookups := g.toLookups
  outerAlloc := by
    change (s.funcs.map Runtime.FuncInst.toCore)[site.outerAddr.value]? = _
    rw [List.getElem?_map, g.outerAlloc]
    simp [Runtime.FuncInst.toCore, Site.coreInstance, func_to_core]
  innerGuard := StraightLine.guard_to_core g.innerGuard

private theorem pending_to_lime (site : Site) (code : List Pending) :
    Wasm.V1.Execution.codeToLime (code.map (site.emit v1Syntax)) = code.map (site.emit limeSyntax) := by
  induction code with
  | nil => rfl
  | cons ins code ih =>
    change Runtime.AdminInstr.map Wasm.V1.Instr.toLime (site.emit v1Syntax ins) ::
      Wasm.V1.Execution.codeToLime (code.map (site.emit v1Syntax)) = _
    rw [ih]
    cases ins with
    | op op => cases op <;> rfl
    | call => rfl

private theorem pending_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (site : Site) (code : List Pending) :
    Wasm.Lime1.Execution.Admin.listToCore s (code.map (site.emit limeSyntax)) =
      code.map (site.emit coreSyntax) := by
  induction code with
  | nil => rfl
  | cons ins code ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (site.emit limeSyntax ins) ++
      Wasm.Lime1.Execution.Admin.listToCore s (code.map (site.emit limeSyntax)) = _
    rw [ih]
    cases ins with
    | op op => cases op <;> rfl
    | call => rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q := by
  open Wasm.V1.Execution in
  cases q with
  | call | invoke =>
    simp only [v1Config, v1Code, limeConfig, limeCode, render, Config.toLime, codeToLime_append, map_values]
    rfl
  | args stack rest =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
      (codeToLime (values stack ++ (site.pending rest).map (site.emit v1Syntax)))]]⟩ :
        Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, map_values, pending_to_lime]
    rfl
  | argumentTrap stack rest =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
      (codeToLime (values stack ++ .trap :: rest.map (site.emit v1Syntax)))]]⟩ :
        Wasm.Lime1.Execution.Config H) = _
    rw [codeToLime_append, map_values]
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller, [.frame site.innerSite.arity site.toSite.frame [.label site.innerSite.arity []
      (Wasm.Lime1.Execution.values stack ++ .trap :: codeToLime (rest.map (site.emit v1Syntax)))]]⟩ :
        Wasm.Lime1.Execution.Config H) = _
    rw [pending_to_lime]
    rfl
  | inner q => exact StraightLine.v1_to_lime s caller site.innerSite q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) (q : State) :
    (limeConfig s caller site q).toCore = coreConfig s.toCore caller site q := by
  open Wasm.Lime1.Execution in
  cases q with
  | call =>
    change (⟨_, _, Admin.listToCore s (values site.args ++ [.source (.call site.outerIndex)])⟩ : Core.Config H) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    rfl
  | invoke =>
    change (⟨_, _, Admin.listToCore s (values site.args ++ [.invoke site.outerAddr])⟩ : Core.Config H) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    have ty : s.funcDefType site.outerAddr = site.type.toDefType := by
      simp [Runtime.Store.funcDefType, Runtime.FuncInst.type, g.outerAlloc]
    change (⟨s.toCore, caller.toCore, coreValues site.args ++ [.ref (.func site.outerAddr.value),
      .callRefType (s.funcDefType site.outerAddr)]⟩ : Core.Config H) = _
    rw [ty]
    rfl
  | args stack rest =>
    change (⟨s.toCore, caller.toCore, [.frame site.innerSite.arity site.toSite.frame.toCore [.label site.innerSite.arity []
      (Admin.listToCore s (values stack ++ (site.pending rest).map (site.emit limeSyntax)))]]⟩ : Core.Config H) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values, pending_to_core]
    rfl
  | argumentTrap stack rest =>
    change (⟨s.toCore, caller.toCore, [.frame site.innerSite.arity site.toSite.frame.toCore [.label site.innerSite.arity []
      (Admin.listToCore s (values stack ++ .trap :: rest.map (site.emit limeSyntax)))]]⟩ : Core.Config H) = _
    rw [CallContinuation.Proofs.core_append, CallContinuation.Proofs.core_values]
    change (⟨s.toCore, caller.toCore, [.frame site.innerSite.arity site.toSite.frame.toCore [.label site.innerSite.arity []
      (coreValues stack ++ .trap :: Admin.listToCore s (rest.map (site.emit limeSyntax)))]]⟩ : Core.Config H) = _
    rw [pending_to_core]
    rfl
  | inner q => exact StraightLine.lime_to_core g.innerGuard q

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Proofs
