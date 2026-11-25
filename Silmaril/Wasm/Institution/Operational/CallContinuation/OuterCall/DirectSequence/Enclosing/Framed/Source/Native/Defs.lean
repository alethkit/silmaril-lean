module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source

open Execution
open Execution.Runtime (Frame)
open Computed (ArgumentSyntax)
open Computed.Sequence (v1Source limeSource coreSource)
open StraightLine

def Body.code {A : Type} {decl : Declaration} (body : Body decl) (ops : ArgumentSyntax A) : List A :=
  (body.saved ++ body.invocation.site.args).map ops.value ++
    ops.call body.invocation.site.index :: body.continuation.map (Sequence.emit ops)

def Body.v1Func {decl : Declaration} (body : Body decl) : Wasm.V1.Func :=
  ⟨decl.typeIndex, decl.locals, body.code v1Source⟩

def Body.limeFunc {decl : Declaration} (body : Body decl) : Wasm.Lime1.Func :=
  ⟨decl.typeIndex, decl.locals, body.code limeSource⟩

def Body.coreFunc {decl : Declaration} (body : Body decl) : Wasm.Func :=
  ⟨decl.typeIndex, decl.locals.map Wasm.V1.ValType.toCore, body.code coreSource⟩

def Body.coreInstance {H : Type} {decl : Declaration} (body : Body decl) : Core.FuncInst H :=
  ⟨decl.type.toDefType, decl.module.toCore, .wasm body.coreFunc⟩

structure Lookups (caller : Frame) (call : Invocation) : Prop where
  typed : Typed call
  resolves : call.target.Resolves caller

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (call : Invocation) : Prop
    extends Lookups caller call where
  allocated : s.funcs[call.target.address.value]? =
    some (.wasm call.target.declaration.type call.target.declaration.module call.body.v1Func)
  scalarResult : call.target.declaration.results.length ≤ 1
  body : Enclosing.V1Guard s call.context call.body.invocation

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (call : Invocation) : Prop
    extends Lookups caller call where
  allocated : s.funcs[call.target.address.value]? =
    some (.wasm call.target.declaration.type call.target.declaration.module call.body.limeFunc)
  body : Enclosing.LimeGuard s call.context call.body.invocation

structure CoreGuard {H : Type} (s : Core.Store H) (caller : Frame) (call : Invocation) : Prop
    extends Lookups caller call where
  allocated : s.funcs[call.target.address.value]? = some call.body.coreInstance
  body : Enclosing.CoreGuard s call.context call.body.invocation

def render {A : Type} {call : Invocation} (source invoke : List A)
    (framed : Framed.State call.context call.body.invocation.site → List A) : State call → List A
  | .call => source
  | .invoke => invoke
  | .framed phase => framed phase

def v1Code (call : Invocation) : State call → List Wasm.V1.Execution.Admin :=
  render (Wasm.V1.Execution.values call.args ++ [.source (.call call.target.index)])
    (Wasm.V1.Execution.values call.args ++ [.invoke call.target.address])
    (Framed.v1Code call.context call.body.invocation.site)

def limeCode (call : Invocation) : State call → List Wasm.Lime1.Execution.Admin :=
  render (Wasm.Lime1.Execution.values call.args ++ [.source (.call call.target.index)])
    (Wasm.Lime1.Execution.values call.args ++ [.invoke call.target.address])
    (Framed.limeCode call.context call.body.invocation.site)

def coreCode (call : Invocation) : State call → List Core.Admin :=
  render (coreValues call.args ++ [.plain (.call call.target.index)])
    (coreValues call.args ++ [.ref (.func call.target.address.value), .callRefType call.target.declaration.type.toDefType])
    (Framed.coreCode call.context call.body.invocation.site)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (call : Invocation) (q : State call) :
    Wasm.V1.Execution.Config H := ⟨s, caller, v1Code call q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (call : Invocation) (q : State call) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode call q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (call : Invocation) (q : State call) :
    Core.Config H := ⟨s, caller.toCore, coreCode call q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source
