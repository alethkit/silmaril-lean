module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open CallContinuation
open CallContinuation.OuterCall (CallTarget)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- A parameterless scalar block with a pending function-label tail. -/
structure Block where
  result : Option NumType
  tail : List Graph.Op

/-- A designated call site in the function label or in one parameterless
scalar block. The block saves the function's initial operand prefix. -/
structure Continuation where
  address : FuncAddr
  owner : Graph.Function
  code : List Graph.Op
  block : Option Block := none

def Continuation.scopes (cont : Continuation) : List (Blocks.Context.Scope Graph.Op) :=
  cont.block.toList.map fun block => ⟨block.result.toList.length, cont.owner.initial, block.tail⟩

def Continuation.fallthrough (cont : Continuation) : List NumType :=
  match cont.block with
  | none => cont.owner.declaration.results
  | some block => block.result.toList

def Continuation.enclosing (cont : Continuation) : Graph.EnclosingLabels :=
  cont.block.toList.map fun _ => cont.owner.declaration.results

def Continuation.blockCheck (cont : Continuation) : Bool :=
  cont.block.all fun block =>
    Graph.checkCode cont.owner.targets cont.owner.localTypes cont.owner.declaration.results
      cont.owner.declaration.results [] (block.result.toList.reverse ++ Prefix.stackTypes cont.owner.initial)
      block.tail .exit cont.owner.declaration.module.types

def Continuation.plug (cont : Continuation) (body : Graph.Body) : Graph.Body :=
  match cont.block with
  | none => body
  | some block => .block cont.owner.initial block.result body block.tail

structure Continuation.Checked (cont : Continuation) (program : Graph.Program)
    (caller : Frame) (saved : List Value) (results : List NumType) : Prop where
  found : program.lookup cont.address = some cont.owner
  module_eq : caller.module = cont.owner.declaration.module
  locals_typed : caller.locals.map Value.type = cont.owner.localTypes
  tail_typed : Graph.checkCode cont.owner.targets cont.owner.localTypes cont.owner.declaration.results
    cont.fallthrough cont.enclosing (results.reverse ++ Prefix.stackTypes saved)
    cont.code .exit cont.owner.declaration.module.types = true
  block_typed : cont.blockCheck = true

/-- The caller activation has already entered, so no direct index is needed to
render it. Its own direct targets are still checked by the graph. -/
def Continuation.target (cont : Continuation) : CallTarget :=
  ⟨⟨0⟩, cont.address, cont.owner.declaration⟩

def Continuation.deliver (cont : Continuation) (saved : List Value) : Nested.Result → Graph.Body
  | .values xs => .running (saved ++ xs) cont.code
  | .trap => .trapped saved cont.code

def Continuation.resume (cont : Continuation) (caller : Frame) (saved : List Value)
    (result : Nested.Result) : Graph.Phase :=
  .label caller.locals (cont.plug (cont.deliver saved result))

/-- The phase records which existing frame relation owns the next native step. -/
inductive Phase
  | callee (phase : Graph.Phase)
  | caller (phase : Graph.Phase)

/-- The frame exit delivers the outcome in one native step. The first step
from the delivered outcome is already a step of the checked caller. -/
inductive Edge (program : Graph.Program) (call : Invocation) (cont : Continuation) : Phase → Phase → Prop
  | callee {a b} (live : a.LabelOutcome) (move : program.FrameEdge call.address a b) :
      Edge program call cont (.callee a) (.callee b)
  | resume {result b} (move : program.FrameEdge cont.address (cont.resume call.caller call.saved result) b) :
      Edge program call cont (.callee (.done result)) (.caller b)
  | caller {a b} (move : program.FrameEdge cont.address a b) :
      Edge program call cont (.caller a) (.caller b)

abbrev Runs (program : Graph.Program) (call : Invocation) (cont : Continuation) :=
  Relation.ReflTransGen (Edge program call cont)

def Continuation.coreWrap {H : Type} (cont : Continuation) (outer : Frame) (body : Core.Config H) : Core.Config H :=
  let n := cont.owner.declaration.results.length
  ⟨body.store, outer.toCore, [.frame n body.frame [.label n [] body.code]]⟩

def Continuation.limeWrap {H : Type} (cont : Continuation) (outer : Frame)
    (body : Wasm.Lime1.Execution.Config H) : Wasm.Lime1.Execution.Config H :=
  let n := cont.owner.declaration.results.length
  ⟨body.store, outer, [.frame n body.frame [.label n [] body.code]]⟩

def Continuation.coreSiteWrap {H : Type} (cont : Continuation) (outer : Frame)
    (body : Core.Config H) : Core.Config H :=
  cont.coreWrap outer (coreNest cont.scopes body)

def Continuation.limeSiteWrap {H : Type} (cont : Continuation) (outer : Frame)
    (body : Wasm.Lime1.Execution.Config H) : Wasm.Lime1.Execution.Config H :=
  cont.limeWrap outer (limeNest cont.scopes body)

def Continuation.coreConfig {H : Type} (cont : Continuation) (call : Invocation)
    (s : Core.Store H) (outer : Frame) : Phase → Core.Config H
  | .callee phase => cont.coreSiteWrap outer (call.coreCallee s (cont.code.map Graph.coreEmit) phase)
  | .caller phase => Graph.coreConfig s outer cont.target phase

def Continuation.limeConfig {H : Type} (cont : Continuation) (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (outer : Frame) : Phase → Wasm.Lime1.Execution.Config H
  | .callee phase => cont.limeSiteWrap outer (call.limeCallee s (cont.code.map Graph.limeEmit) phase)
  | .caller phase => Graph.limeConfig s outer cont.target phase

def Continuation.corePrefix {H : Type} (cont : Continuation) (call : Invocation)
    (s : Core.Store H) (outer : Frame) : List (Core.Config H) :=
  (call.corePrefix s (cont.code.map Graph.coreEmit)).map (cont.coreSiteWrap outer)

def Continuation.limePrefix {H : Type} (cont : Continuation) (call : Invocation)
    (s : Wasm.Lime1.Execution.Store H) (outer : Frame) : List (Wasm.Lime1.Execution.Config H) :=
  (call.limePrefix s (cont.code.map Graph.limeEmit)).map (cont.limeSiteWrap outer)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume
