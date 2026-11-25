module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs

open Execution
open Execution.Runtime (Frame)
open StraightLine
open Computed.Sequence (v1Source limeSource coreSource)

private theorem func_to_lime (p : Program) : p.v1Func.toLime = p.limeFunc := by
  have body : Wasm.V1.Expr.toLime p.v1Func.body = p.limeFunc.body := by
    change Wasm.V1.Expr.toLime (p.body v1Source) = p.body limeSource
    simp only [Program.body, Wasm.V1.Expr.toLime_eq_map, List.map_map]
    apply List.map_congr_left
    intro ins _
    cases ins with
    | numeric op => cases op <;> rfl
    | call => rfl
  exact congrArg (fun body => (⟨p.site.typeIndex, p.site.locals, body⟩ : Wasm.Lime1.Func)) body

private theorem func_to_core (p : Program) : p.limeFunc.toCore = p.coreFunc := by
  have body : Wasm.Lime1.Expr.toCore p.limeFunc.body = p.coreFunc.body := by
    change Wasm.Lime1.Expr.toCore (p.body limeSource) = p.body coreSource
    simp only [Program.body, Wasm.Lime1.Expr.toCore_eq_map, List.map_map]
    apply List.map_congr_left
    intro ins _
    cases ins with
    | numeric op => cases op <;> rfl
    | call => rfl
  exact congrArg (fun body => (⟨p.site.typeIndex, p.site.locals.map Wasm.V1.ValType.toCore, body⟩ : Wasm.Func)) body

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {p : Program}
    (g : V1Guard s caller p) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller p where
  toLookups := g.toLookups
  allocated := by
    rw [Runtime.Store.mapCode_funcs_getElem?, g.allocated]
    simp [Runtime.FuncInst.mapCode, func_to_lime]
  body := Sequence.guard_to_lime g.body

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    (g : LimeGuard s caller p) : CoreGuard s.toCore caller p where
  toLookups := g.toLookups
  allocated := by
    change (s.funcs.map Runtime.FuncInst.toCore)[p.site.address.value]? = _
    rw [List.getElem?_map, g.allocated]
    simp [Runtime.FuncInst.toCore, Program.coreInstance, func_to_core]
  body := Sequence.guard_to_core g.body

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site)
    (q : State site) :
    (v1Config s caller site q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q := by
  have mapped (a : Sequence.State site.body) :
      Wasm.V1.Execution.codeToLime (Sequence.v1Code site.body a) =
        Sequence.limeCode site.body a :=
    congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) (Sequence.v1_to_lime s site.body a)
  cases q with
  | call | invoke =>
    simp only [v1Config, v1Code, limeConfig, limeCode, render, Wasm.V1.Execution.Config.toLime,
      Wasm.V1.Execution.codeToLime_append, Wasm.V1.Execution.map_values]
    rfl
  | label a =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, caller,
      [.frame site.arity site.frame [.label site.arity [] (Wasm.V1.Execution.codeToLime (Sequence.v1Code site.body a))]]⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [mapped]
    rfl
  | exit r =>
    cases r with
    | trap => rfl
    | values stack =>
      change (⟨s.mapCode Wasm.V1.Func.toLime, caller,
        [.frame site.arity site.frame (Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values stack))]⟩ :
        Wasm.Lime1.Execution.Config H) = _
      rw [Wasm.V1.Execution.map_values]
      rfl
  | done r =>
    cases r with
    | trap => rfl
    | values stack =>
      exact congrArg (fun code => (⟨s.mapCode Wasm.V1.Func.toLime, caller, code⟩ :
        Wasm.Lime1.Execution.Config H)) (Wasm.V1.Execution.map_values stack)

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {p : Program}
    (g : LimeGuard s caller p) (q : State p.site) :
    (limeConfig s caller p.site q).toCore =
      coreConfig s.toCore caller p.site q := by
  have mapped (a : Sequence.State p.site.body) : Wasm.Lime1.Execution.Admin.listToCore s
      (Sequence.limeCode p.site.body a) = Sequence.coreCode p.site.body a :=
    congrArg Core.Config.code (Sequence.lime_to_core g.body a)
  cases q with
  | call =>
    change (⟨_, _, Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.values p.site.args ++ [.source (.call p.site.index)])⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore]
    rfl
  | invoke =>
    change (⟨_, _, Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.values p.site.args ++ [.invoke p.site.address])⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore]
    have ty : s.funcDefType p.site.address = p.site.type.toDefType := by
      simp [Runtime.Store.funcDefType, Runtime.FuncInst.type, g.allocated]
    change (⟨s.toCore, caller.toCore, coreValues p.site.args ++ [.ref (.func p.site.address.value),
      .callRefType (s.funcDefType p.site.address)]⟩ : Core.Config H) = _
    rw [ty]
    rfl
  | label a =>
    change (⟨s.toCore, caller.toCore, [.frame p.site.arity p.site.frame.toCore [.label p.site.arity []
      (Wasm.Lime1.Execution.Admin.listToCore s (Sequence.limeCode p.site.body a))]]⟩ : Core.Config H) = _
    rw [mapped]
    rfl
  | exit r =>
    cases r with
    | trap => rfl
    | values stack =>
      change (⟨s.toCore, caller.toCore, [.frame p.site.arity p.site.frame.toCore
        (Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values stack))]⟩ : Core.Config H) = _
      rw [CallContinuation.values_toCore]
      rfl
  | done r =>
    cases r with
    | trap => rfl
    | values stack =>
      exact congrArg (fun code => (⟨s.toCore, caller.toCore, code⟩ : Core.Config H))
        (CallContinuation.values_toCore s stack)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Proofs
