module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Code
import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs

open Execution
open Execution.Runtime (Frame)
open Computed.Sequence (v1Source limeSource coreSource)

theorem func_to_lime {decl : Declaration} (body : Body decl) : body.v1Func.toLime = body.limeFunc := by
  have code : Wasm.V1.Expr.toLime (body.code v1Source) = body.code limeSource := by
    rw [Wasm.V1.Expr.toLime_eq_map]
    exact map_code body v1Source limeSource Wasm.V1.Instr.toLime
      (fun ⟨t, bits⟩ => by cases t <;> rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  exact congrArg (fun code => (⟨decl.typeIndex, decl.locals, code⟩ : Wasm.Lime1.Func)) code

theorem func_to_core {decl : Declaration} (body : Body decl) : body.limeFunc.toCore = body.coreFunc := by
  have code : Wasm.Lime1.Expr.toCore (body.code limeSource) = body.code coreSource := by
    rw [Wasm.Lime1.Expr.toCore_eq_map]
    exact map_code body limeSource coreSource Wasm.Lime1.Instr.toCore
      (fun ⟨t, bits⟩ => by cases t <;> rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  exact congrArg (fun code => (⟨decl.typeIndex, decl.locals.map Wasm.V1.ValType.toCore, code⟩ : Wasm.Func)) code

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {call : Invocation}
    (g : V1Guard s caller call) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller call where
  toLookups := g.toLookups
  allocated := by
    rw [Runtime.Store.mapCode_funcs_getElem?, g.allocated]
    simp [Runtime.FuncInst.mapCode, func_to_lime]
  body := Enclosing.guard_to_lime g.body

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    (g : LimeGuard s caller call) : CoreGuard s.toCore caller call where
  toLookups := g.toLookups
  allocated := by
    change (s.funcs.map Runtime.FuncInst.toCore)[call.target.address.value]? = _
    rw [List.getElem?_map, g.allocated]
    simp [Runtime.FuncInst.toCore, Body.coreInstance, func_to_core]
  body := Enclosing.guard_to_core g.body

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (call : Invocation) (q : State call) :
    (v1Config s caller call q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller call q := by
  open Wasm.V1.Execution in
  cases q with
  | call | invoke =>
    simp only [v1Config, v1Code, limeConfig, limeCode, render, Config.toLime, codeToLime_append, map_values]
    rfl
  | framed q => exact Framed.v1_to_lime s caller call.context call.body.invocation.site q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {call : Invocation}
    (g : LimeGuard s caller call) (q : State call) :
    (limeConfig s caller call q).toCore = coreConfig s.toCore caller call q := by
  open Wasm.Lime1.Execution in
  cases q with
  | call =>
    change (⟨_, _, Admin.listToCore s (values call.args ++ [.source (.call call.target.index)])⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore]
    rfl
  | invoke =>
    change (⟨_, _, Admin.listToCore s (values call.args ++ [.invoke call.target.address])⟩ : Core.Config H) = _
    rw [CallContinuation.listToCore_append, CallContinuation.values_toCore]
    have ty : s.funcDefType call.target.address = call.target.declaration.type.toDefType := by
      simp [Runtime.Store.funcDefType, Runtime.FuncInst.type, g.allocated]
    change (⟨s.toCore, caller.toCore, coreValues call.args ++ [.ref (.func call.target.address.value),
      .callRefType (s.funcDefType call.target.address)]⟩ : Core.Config H) = _
    rw [ty]
    rfl
  | framed q => exact Framed.lime_to_core caller g.body q

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Proofs
