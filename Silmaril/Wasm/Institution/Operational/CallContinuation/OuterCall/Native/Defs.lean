module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall

open Execution
open Execution.Runtime (Frame Value FuncAddr)

def Outer.type (fn : Outer) : Wasm.V1.FuncType := ⟨fn.params, fn.inner.result.toList⟩

def Outer.frame (fn : Outer) (args : List Value) : Runtime.Frame :=
  ⟨args ++ fn.locals.map Value.zero, fn.moduleInst⟩

def Outer.coreBody (fn : Outer) : List Wasm.Instr :=
  (Locals.values fn.innerArgs).map Locals.coreInstr ++ [.call fn.innerIndex, .nop]

def Outer.coreFunc (fn : Outer) : Wasm.Func :=
  ⟨fn.typeIndex, fn.locals.map Wasm.V1.ValType.toCore, fn.coreBody⟩

def Outer.coreInstance {H : Type} (fn : Outer) : Core.FuncInst H :=
  ⟨fn.type.toDefType, fn.moduleInst.toCore, .wasm fn.coreFunc⟩

abbrev coreValues (xs : List Value) := Core.vals (xs.map Value.toCore)

def coreUnresolved {H : Type} (s : Core.Store H) (caller : Runtime.Frame) (i : FuncIdx) (args : List Value) :
    Core.Config H := ⟨s, caller.toCore, coreValues args ++ [.plain (.call i)]⟩

def coreResolved {H : Type} (s : Core.Store H) (caller : Runtime.Frame) (a : FuncAddr)
    (fn : Outer) (args : List Value) : Core.Config H :=
  ⟨s, caller.toCore, coreValues args ++ [.ref (.func a.value), .callRefType fn.type.toDefType]⟩

def coreEntered {H : Type} (s : Core.Store H) (caller : Runtime.Frame)
    (fn : Outer) (args : List Value) : Core.Config H :=
  ⟨s, caller.toCore, [.frame fn.arity (fn.frame args).toCore
    [.label fn.arity [] (coreValues fn.innerArgs ++ [.plain (.call fn.innerIndex), .plain .nop])]]⟩

def limeBody (fn : Outer) : List Wasm.Lime1.Instr :=
  (Locals.values fn.innerArgs).map Locals.limeInstr ++ [.call fn.innerIndex, .nop]

def limeFunc (fn : Outer) : Wasm.Lime1.Func := ⟨fn.typeIndex, fn.locals, limeBody fn⟩

def limeUnresolved {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (i : FuncIdx) (args : List Value) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, Wasm.Lime1.Execution.values args ++ [.source (.call i)]⟩

def limeResolved {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (a : FuncAddr) (args : List Value) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, Wasm.Lime1.Execution.values args ++ [.invoke a]⟩

def limeEntered {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (fn : Outer) (args : List Value) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, [.frame fn.arity (fn.frame args)
      [.label fn.arity [] (Wasm.Lime1.Execution.values fn.innerArgs ++ [.source (.call fn.innerIndex), .source .nop])]]⟩

structure CoreGuard {H : Type} (s : Core.Store H) (caller : Runtime.Frame) (site : CallSite) : Prop where
  typed : Typed site
  outerLookup : caller.module.funcs[site.outerIndex.toNat]? = some site.outerAddr
  innerLookup : site.callee.moduleInst.funcs[site.callee.innerIndex.toNat]? = some site.innerAddr
  outerAlloc : s.funcs[site.outerAddr.value]? = some site.callee.coreInstance
  innerAlloc : s.funcs[site.innerAddr.value]? = some site.callee.inner.coreInstance

def coreConfig {H : Type} (s : Core.Store H) (caller : Runtime.Frame) (site : CallSite) :
    State → Core.Config H
  | .call => coreUnresolved s caller site.outerIndex site.args
  | .invoke => coreResolved s caller site.outerAddr site.callee site.args
  | .entered => coreEntered s caller site.callee site.args
  | .nested phase =>
      Nested.coreConfig s caller (site.callee.frame site.args) site.innerAddr
        site.callee.inner site.callee.arity phase

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : CallSite) : Prop where
  typed : Typed site
  outerLookup : caller.module.funcs[site.outerIndex.toNat]? = some site.outerAddr
  innerLookup : site.callee.moduleInst.funcs[site.callee.innerIndex.toNat]? = some site.innerAddr
  outerAlloc : s.funcs[site.outerAddr.value]? = some (.wasm site.callee.type site.callee.moduleInst (limeFunc site.callee))
  innerAlloc : s.funcs[site.innerAddr.value]? = some (.wasm site.callee.inner.type site.callee.inner.module site.callee.inner.limeFunc)

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : CallSite) :
    State → Wasm.Lime1.Execution.Config H
  | .call => limeUnresolved s caller site.outerIndex site.args
  | .invoke => limeResolved s caller site.outerAddr site.args
  | .entered => limeEntered s caller site.callee site.args
  | .nested phase =>
      Nested.limeConfig s caller (site.callee.frame site.args) site.innerAddr
        site.callee.inner site.callee.arity phase

def v1Func (fn : Outer) : Wasm.V1.Func :=
  ⟨fn.typeIndex, fn.locals, (Locals.values fn.innerArgs).map Locals.v1Instr ++ [.call fn.innerIndex, .nop]⟩

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : CallSite) : Prop where
  typed : Typed site
  outerLookup : caller.module.funcs[site.outerIndex.toNat]? = some site.outerAddr
  innerLookup : site.callee.moduleInst.funcs[site.callee.innerIndex.toNat]? = some site.innerAddr
  outerAlloc : s.funcs[site.outerAddr.value]? = some (.wasm site.callee.type site.callee.moduleInst (v1Func site.callee))
  innerAlloc : s.funcs[site.innerAddr.value]? = some (.wasm site.callee.inner.type site.callee.inner.module site.callee.inner.v1Func)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : CallSite) :
    State → Wasm.V1.Execution.Config H
  | .call => ⟨s, caller, Wasm.V1.Execution.values site.args ++ [.source (.call site.outerIndex)]⟩
  | .invoke => ⟨s, caller, Wasm.V1.Execution.values site.args ++ [.invoke site.outerAddr]⟩
  | .entered =>
    ⟨s, caller, [.frame site.callee.arity (site.callee.frame site.args)
      [.label site.callee.arity [] (Wasm.V1.Execution.values site.callee.innerArgs ++
        [.source (.call site.callee.innerIndex), .source .nop])]]⟩
  | .nested phase =>
      Nested.v1Config s caller (site.callee.frame site.args) site.innerAddr
        site.callee.inner site.callee.arity phase

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
